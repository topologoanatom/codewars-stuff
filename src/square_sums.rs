use rand::seq::SliceRandom;

const TEST_LIMIT: usize = 1300;
const SQUARES: [bool; TEST_LIMIT * 2 + 1] = mark_squares();

const fn is_perfect_square_lookup(n: u32) -> bool {
    debug_assert!((n as usize) <= SQUARES.len());
    SQUARES[(n - 1) as usize]
}

const fn mark_squares<const N: usize>() -> [bool; N] {
    let mut res = [false; N];
    let mut i = 0;

    while i < N {
        res[i] = is_perfect_square(i as u32 + 1);
        i += 1;
    }

    res
}

const fn is_perfect_square(n: u32) -> bool {
    // check for quadratic residues mod 64
    const VALID_RESIDUES: &[u32] = &[0, 1, 4, 9, 16, 17, 25, 33, 36, 41, 49, 57];

    let mut i = 0;
    let mut found = false;
    let residue = n & 0x3F;

    while i < VALID_RESIDUES.len() {
        found |= VALID_RESIDUES[i] == residue;
        i += 1;
    }

    if !found {
        return false;
    }

    let root = n.isqrt();
    root * root == n
}

fn square_table(n: u32) -> (Vec<u32>, Vec<usize>) {
    let mut res = Vec::with_capacity(n as usize);
    let square_checker = |x: u32| {
        if n as usize <= TEST_LIMIT {
            is_perfect_square_lookup(x)
        } else {
            is_perfect_square(x)
        }
    };

    for i in 1..=n {
        let mut row = Vec::new();
        for j in 1..=n {
            if i == j {
                continue;
            }
            if square_checker(i + j) {
                row.push(j - 1);
            }
        }
        res.push(row);
    }

    // sort by node degree in ascending order
    let degrees = res.iter().map(|row| row.len()).collect::<Vec<_>>();
    res.iter_mut()
        .for_each(|row| row.sort_by(|a, b| degrees[*a as usize].cmp(&degrees[*b as usize])));

    let mut flattened = Vec::with_capacity(res.iter().map(|row| row.len()).sum());
    let sizes = res.iter().map(|row| row.len()).collect();
    res.iter().for_each(|row| flattened.extend_from_slice(row));

    (flattened, sizes)
}

/// Let x and y be neighbours if x + y is perfect square
/// Let degree of x is number of it's neighbours
/// - `lookup_table` - for each x up to n stores list of all x's neighbours
/// - `used_variants` - for each x up to n stores how many x's neighbours are used (neighbours are taken from the start).
///   `None` if x was not used yet
/// - `current_num` - last pushed candidate (stored as index, i.e. x - 1)
/// - `visited_count` - how many nodes is already used
/// - `unused_neighbours_count` - how many unused neighbours x node has
struct Backtracker<'a> {
    neighbours_lookup: &'a [&'a [u32]],
    used_neigbours_idx: Vec<Option<usize>>,
    current_num: usize,
    visited_count: usize,
    unused_neighbours_count: Vec<u32>,
}

impl<'a> Backtracker<'a> {
    fn new(neighbours_lookup: &'a [&'a [u32]], current_num: usize) -> Self {
        let unused_neighbours_count = neighbours_lookup
            .iter()
            .map(|x| x.len() as u32)
            .collect::<Vec<_>>();
        let mut res = Self {
            neighbours_lookup,
            used_neigbours_idx: vec![None; neighbours_lookup.len()],
            current_num,
            visited_count: 1,
            unused_neighbours_count,
        };

        res.mark_as_used(current_num);
        res
    }

    /// Tries to return next possible neighbour to `current_num` by incrementing it's
    /// `used_variants` counter.
    fn advance(&mut self) -> Option<u32> {
        let curr = self.current_num;
        let next_pos = match self.used_neigbours_idx[curr] {
            Some(x) => x + 1,
            None => 0,
        };

        if next_pos < self.neighbours_lookup[curr].len() {
            self.used_neigbours_idx[curr] = Some(next_pos);
            return Some(self.neighbours_lookup[curr][next_pos]);
        }

        None
    }

    #[inline]
    /// For given num counts how many yet unused neighbours it has
    fn count_neighbours(&self, num: usize) -> u32 {
        self.unused_neighbours_count[num]
    }

    #[inline]
    fn mark_as_used(&mut self, num: usize) {
        for &neighbour in self.neighbours_lookup[num] {
            self.unused_neighbours_count[neighbour as usize] -= 1;
        }
    }

    #[inline]
    fn mark_as_unused(&mut self, num: usize) {
        for &neighbour in self.neighbours_lookup[num] {
            self.unused_neighbours_count[neighbour as usize] += 1;
        }
    }

    /// Checks wheter its worth to push given num to result.
    /// Returns `false` if `next_num`:
    /// 1. is already used
    /// 2. pushing `next_num` to sequence causes any unvisited number
    ///     * have degree 0 or
    ///     * two or more unvisited numbers have degree 1 (unless its last number)
    fn jump(&mut self, next_num: usize) -> bool {
        if self.used_neigbours_idx[next_num].is_some() {
            return false;
        }

        let mut one_degree_count = 0;
        let total_nodes = self.neighbours_lookup.len();
        let visited_count = self.visited_count + 1;

        // this loop can be potenitally optimized by traversing only over neighbours
        // but this complicates 1-degree node tracking so I have dropped it for now
        for i in 0..total_nodes {
            if i == next_num || self.used_neigbours_idx[i].is_some() {
                continue;
            }

            let deg = self.count_neighbours(i);

            if deg == 0 && visited_count < total_nodes {
                return false;
            }

            if deg == 1 {
                one_degree_count += 1;
            }

            if one_degree_count > 1 && visited_count < total_nodes {
                return false;
            }
        }

        self.mark_as_used(next_num);
        self.visited_count += 1;
        self.current_num = next_num;
        true
    }

    /// Mark `current_num` unused and return to given num.
    /// Assumes that `prev_num` is indeed used
    #[inline]
    fn backtrack_to(&mut self, prev_num: usize) {
        self.mark_as_unused(self.current_num);
        self.visited_count -= 1;
        self.used_neigbours_idx[self.current_num] = None;
        self.current_num = prev_num;
    }
}

fn backtrack_aux(
    n: u32,
    squares_table: &[&[u32]],
    first_backtrack: &mut Vec<u32>,
) -> Option<Vec<u32>> {
    const BACKTRACK_LIMIT: u32 = 5_000;
    let mut res = Vec::with_capacity(n as usize);

    let mut iter = 0;
    while let Some(x) = first_backtrack.pop() {
        let mut backtracker = Backtracker::new(squares_table, x as usize);

        res.push(x);

        while res.len() != n as usize && !res.is_empty() && iter < BACKTRACK_LIMIT {
            if let Some(next) = backtracker.advance() {
                if backtracker.jump(next as usize) {
                    res.push(next);
                }
            } else {
                res.pop();
                if let Some(last) = res.last() {
                    backtracker.backtrack_to(*last as usize);
                }
                iter += 1;
            }
        }

        if iter > BACKTRACK_LIMIT {
            return None;
        }

        if res.len() == n as usize {
            res.iter_mut().for_each(|x| *x += 1);
            return Some(res);
        }
    }

    None
}

/// Can produce false negatives
pub fn backtrack(n: u32) -> Option<Vec<u32>> {
    const TRIALS: usize = 10;
    // create row slices from flat data
    let (flat_data, sizes) = square_table(n);
    let mut curr_len = 0;
    let squares_table = sizes
        .iter()
        .map(|size| {
            curr_len += size;
            &flat_data[(curr_len - size)..curr_len]
        })
        .collect::<Vec<_>>();

    let mut rng = rand::rng();

    for _ in 0..TRIALS {
        let mut first_backtrack = (0..n).collect::<Vec<_>>();
        first_backtrack.shuffle(&mut rng);
        if let Some(res) = backtrack_aux(n, &squares_table, &mut first_backtrack) {
            return Some(res);
        }
    }

    None
}

#[cfg(test)]
mod test {
    use super::*;

    fn is_valid_sequence(seq: &[u32]) -> bool {
        seq.windows(2).all(|pair| {
            if let [x, y] = pair {
                is_perfect_square(x + y)
            } else {
                true
            }
        })
    }

    #[test]
    fn test_square_sums() {
        let n = 15;
        let seq = backtrack(n);

        assert!(seq.is_some_and(|x| is_valid_sequence(&x)));
    }

    #[cfg(not(debug_assertions))]
    #[test]
    fn test_big_square_sums() {
        let n = 20_000;
        let seq = backtrack(n);

        if let Some(seq) = seq {
            assert!(is_valid_sequence(&seq));
        }
    }
}
