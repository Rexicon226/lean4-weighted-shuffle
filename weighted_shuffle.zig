const std = @import("std");
const chacha = @import("chacha.zig");

/// See comment above `ChaCha.uniform` to understand the difference.
pub const Mode = enum {
    mod,
    shift,
};

/// This is a (nearly) direct port of Firedancer's weighted shuffle approach. It can be found here:
/// https://github.com/firedancer-io/firedancer/blob/805077c9e9d448ec9eeb0fa1fe7d0c519ad917e6/src/ballet/wsample/fd_wsample.c
///
/// They already provide a very useful comment, which explains a lot of the general idea,
/// and I hope to elaborate on it a bit further with my comment, and then go into a more thorough
/// explanation of how the implementation itself works.
///
/// The `SamplerTree` solves a problem called **weighted sampling**. Think of the problem like this,
/// - You have a collection of items, each with a weight.
/// - You want to pick items randomly, but proportionally to their weight.
/// - Somtimes you want to pick items without replacement (once picked, remove them).
///
/// Our approach is to store weights in a radix tree (here with radix being `R`), laid out
/// in a flat array like a heap. Each internal node stores *prefix sums* of its children's
/// weights (called `left_sum` here, since they go left to right), which allows us to locate an
/// item by binary searching over the sums. This turns sampling into a predictable sequence of
/// comparisons that run in `O(height)` time, with very few branches.
///
/// To add items:
/// Walk up the tree, updating all affected prefix sums.
///
/// To sample:
/// Generate a uniform random value in `[0, total_weight)`, where the total weight can
/// be easily found by just looking at the sum weight in the root node, descend the tree
/// by checking which child interval contains it, then repeat until a leaf is found.
///
/// To remove:
/// Recover the exact weight of the chosen item, then walk up the tree subtracting it
/// from the relevant prefix sums.
///
/// Because the tree is stored as an array, no dynamic allocations are needed and the cache
/// locality of excellet. Using a radix of `9` seems to be a sweet spot: it keeps the height
/// low while leeting each node fit neatly into a AVX512 register.
///
/// A bit of further "nerding out" about the math behind the tree:
///
/// Perhaps instead of thinking of the tree in terms of cool indexing tricks, think about it
/// in terms of mathematical invariants. At it's core the tree is encoding partial sums: every interval
/// node represents the sum of a disjoint subset of the leaves, and these subsets always partition the whole
/// array. That means the value at the root is the sum of everything, but more importantly, the decomposition
/// into nodes gives us a unique factorization of any prefix sum.
///
/// The sampling algorithm can be distilled into basically:
///
/// 1. Draw `x \in [0, S)` (root uses S = total_weight).
/// 2. Compute: `m = #{k \in {0, ..., R - 2}: Lk <= x}`.
///     In plain terms: "m is the number of stored prefix sums Lk that are less than or equal to the current random value `x`".
/// 3.That `m` is the child index to descend to (so `m \in {0, ..., R - 1}`).
/// 4. Replace `x <- x - L(m - 1)`, set `S <- Lm - L(m - 1)`. Recurse into child `m`.
///
/// The prefix sums partition the interval `[0, S)` into `R` disjoint ranges:
/// ```ascii
/// [0, L0), [L0, L1), ..., [L(R - 2), S)
/// ```
/// By construction these intervals are contiguous and non-overlapping and their lengths are always:
/// ```ascii
/// w0, w1, ..., w(R - 1)
/// ```
///
/// The defintion of `m` (count of stored `Lk <= x`) yields the unique `m` such that :
/// ```ascii
/// L(m - 1) <= x < Lm
/// ```
/// (If `x < L0`, then none of the stored `Lk` satisfy `Lk <= x`, so `m = 0`; Same thing applies
/// if `x` is larger than `L(R - 2)`, we set `m = R - 1`, this allows us to store 8 prefix sums instead of 9).
///
/// This definition (with only 8 prefix sums instead of 9), let's us perform the search with only a few
/// AVX512 instructions, `vpcmp` and `vpopcnt`. The `@popCount` optimization is really neat, because
/// it lets us directly map into the sums.
///
/// - If `x < L0`, then the whole vector is false, so `popcount(k) = 0`, thus we go to child 0.
/// - If `Lj <= x < L(j + 1)`, then exactly `j + 1` stored checks are true, thus `popcount(k) = j + 1`,
/// and thus we go to child `j + 1.`
/// - Same rules as described above here, if `x` is too larger, the `popcount` will be `R - 1`, and so
/// we go to child `R - 1`.
///
/// TODO: describe `findWeight`
/// TODO: maybe describe the costs and complexities and stuff
///
pub fn SamplerTree(mode: Mode) type {
    return struct {
        tree: [8]Element, // TODO: compute size correctly

        total_count: u64,
        total_weight: u64,
        unremoved_count: u64,
        unremoved_weight: u64,

        internal_node_count: u64,
        height: u64,

        rng: chacha.ChaCha(.twenty),

        const Self = @This();

        /// The radix of the tree. This implementation is fully generic over the radix, but performance
        /// will be really bad if it isn't on the `1+2^n` line, and `9` works well empirically, especially
        /// because it allows a child's sums to fit into AV512 registers, `(R - 1) * 64 == 512`.
        const R = 9;

        const V = @Vector(R - 1, u64);
        const C = @Vector(R - 1, u16);
        const Pair = struct { index: u64, weight: u64 };

        const Element = struct {
            left_sum: [R - 1]u64,

            const zero: Element = .{ .left_sum = @splat(0) };
        };

        pub fn init(num_elements: u64) Self {
            const height, const internal_count = computeHeight(num_elements);
            return .{
                .tree = @splat(.zero), // zero out the tree

                .total_count = 0,
                .total_weight = 0,
                .unremoved_count = 0,
                .unremoved_weight = 0,

                .internal_node_count = internal_count,
                .height = height,

                .rng = .init(@splat(0)),
            };
        }

        pub fn deinit(self: *Self) void {
            _ = self;
        }

        fn computeHeight(num_elements: u64) struct { u64, u64 } {
            var height: u64 = 0;
            var internal: u64 = 0;
            var powRh: u64 = 1; // R^height
            while (num_elements > powRh) {
                internal += powRh;
                powRh *= R;
                height += 1;
            }
            return .{ height, internal };
        }

        pub fn addWeight(self: *Self, weight: u64) void {
            std.debug.assert(weight != 0);

            var i = self.internal_node_count + self.unremoved_count;
            for (0..self.height) |_| {
                const parent = (i - 1) / R;
                // const child_index = (i - 1) - (R * parent); // in [0, R)
                const child_index = (i - 1) % R;
                for (child_index..R - 1) |k| self.tree[parent].left_sum[k] += weight;
                i = parent;
            }

            self.unremoved_count += 1;
            self.total_count += 1;
            self.unremoved_weight += weight;
            self.total_weight += weight;
        }

        pub fn sample(self: *Self) !u64 {
            if (self.unremoved_weight == 0) return error.Empty;
            const uniform = self.rng.roll(mode, self.unremoved_weight);
            return self.mapSample(uniform).index;
        }

        fn mapSample(self: *Self, input: u64) Pair {
            var cursor: u64 = 0;
            var query: u64 = input;
            var S: u64 = self.unremoved_weight;
            for (0..self.height) |_| {
                const e = self.tree[cursor];
                const x: u64 = query;

                // TODO: clean this up, maybe
                const mask: u8 = @bitCast(@as(V, e.left_sum) <= @as(V, @splat(x)));
                const child_index: u64 = @popCount(mask);

                // TODO: explore firedancer's branchless approach here, although i doubt i'll use it. perf?
                const li = if (child_index < R - 1) e.left_sum[child_index] else S;
                const lm1 = if (child_index > 0) e.left_sum[child_index - 1] else 0;

                query -= lm1;
                S = li - lm1;
                cursor = (R * cursor) + child_index + 1;
            }
            return .{
                .index = cursor - self.internal_node_count,
                .weight = S,
            };
        }

        pub fn remove(self: *Self, idx: u64) void {
            const weight = self.findWeight(idx);
            self.removePair(.{ .weight = weight, .index = idx });
        }

        fn findWeight(self: *Self, idx: u64) u64 {
            var cursor = idx + self.internal_node_count;
            var lm1: u64 = 0;
            var li: u64 = self.unremoved_weight;

            for (0..self.height) |_| {
                const parent = (cursor - 1) / R;
                const child_index = (cursor - 1) - (R * parent); // in [0, R)

                lm1 += if (child_index > 0) self.tree[parent].left_sum[child_index - 1] else 0;
                if (child_index < R - 1) {
                    li = self.tree[parent].left_sum[child_index];
                    break;
                }

                cursor = parent;
            }

            return li - lm1;
        }

        pub fn removePair(self: *Self, to_remove: Pair) void {
            var cursor = to_remove.index + self.internal_node_count;

            for (0..self.height) |_| {
                const parent = (cursor - 1) / R;
                const child_index = (cursor - 1) - (R * parent); // in [0, R)

                const indices: C = @splat(@truncate(child_index));
                const weight: V = @splat(to_remove.weight);
                const left_sum: V = self.tree[parent].left_sum;
                self.tree[parent].left_sum = @select(
                    u64,
                    indices < std.simd.iota(u16, R - 1) + @as(C, @splat(1)),
                    left_sum -% weight,
                    left_sum,
                );

                cursor = parent;
            }
            self.unremoved_count -|= 1;
            self.unremoved_weight -= to_remove.weight;
        }

        pub fn sampleAndRemove(self: *Self) ?u64 {
            if (self.unremoved_weight == 0) return null;
            const uniform = self.rng.roll(mode, self.unremoved_weight);
            const pair = self.mapSample(uniform);
            self.removePair(pair);
            return pair.index;
        }
    };
}

pub fn main() !void {
    const S = SamplerTree(.mod);

    var example = S.init(10);
    example.addWeight(3);
    // example.addWeight(10);

    for (example.tree) |r| {
        for (r.left_sum) |e| std.debug.print("{:0>4} ", .{e});
        std.debug.print("\n", .{});
    }

    std.debug.print("sample: {}\n", .{try example.sample()});

    std.debug.print("unremoved weight: {}\n", .{example.unremoved_weight});
}
