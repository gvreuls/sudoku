mod lib {
    const ROOT: usize = 3;
    const DIM: usize = ROOT * ROOT;
    const DIM2: usize = DIM * DIM;
    const BEST_THRESHOLD: usize = (DIM + ROOT - 1) * ROOT + 1;

    #[derive(Debug, Clone, Copy)]
    pub struct Coords {
        i: u32,
        r: u32,
        c: u32,
        b: u32,
    }

    impl Coords {
        pub const START: Self = Self { i: 0, r: 0, c: 0, b: 0 };
        #[rustfmt::skip]
        const BOX: [u32; DIM2] = [
            0, 0, 0, 1, 1, 1, 2, 2, 2,
            0, 0, 0, 1, 1, 1, 2, 2, 2,
            0, 0, 0, 1, 1, 1, 2, 2, 2,
            3, 3, 3, 4, 4, 4, 5, 5, 5,
            3, 3, 3, 4, 4, 4, 5, 5, 5,
            3, 3, 3, 4, 4, 4, 5, 5, 5,
            6, 6, 6, 7, 7, 7, 8, 8, 8,
            6, 6, 6, 7, 7, 7, 8, 8, 8,
            6, 6, 6, 7, 7, 7, 8, 8, 8,
        ];

        #[inline(always)]
        #[must_use]
        pub const fn new(row: u32, column: u32) -> Self {
            Self::new_indexed(row, column, row * DIM as u32 + column)
        }

        #[inline(always)]
        #[must_use]
        const fn new_indexed(row: u32, column: u32, index: u32) -> Self {
            debug_assert!(row < DIM as u32 && column < DIM as u32 && index < DIM2 as u32);
            Self {
                i: index,
                r: row,
                c: column,
                b: unsafe { *Self::BOX.as_ptr().add(index as usize) },
            }
        }

        #[inline(always)]
        #[must_use]
        pub const fn next(self) -> Option<Self> {
            if self.c < 8 {
                Some(Self::new_indexed(self.r, self.c + 1, self.i + 1))
            } else if self.r < 8 {
                Some(Self::new_indexed(self.r + 1, 0, self.i + 1))
            } else {
                None
            }
        }
    }

    impl PartialEq for Coords {
        #[inline(always)]
        fn eq(&self, rhs: &Self) -> bool {
            self.i == rhs.i
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq)]
    pub struct BitVec(u16);

    impl BitVec {
        pub const ALL_SET: Self = Self((1 << DIM) - 1);

        #[inline(always)]
        #[must_use]
        pub const fn new_mask(bit_mask: u16) -> Self {
            debug_assert!(bit_mask <= Self::ALL_SET.0);
            Self(bit_mask)
        }

        #[inline(always)]
        #[must_use]
        pub const fn new_bit(bit_index: u8) -> Self {
            debug_assert!(bit_index < DIM as u8);
            Self(1 << bit_index)
        }

        #[inline(always)]
        #[must_use]
        pub const fn is_empty(self) -> bool {
            self.0 == 0
        }

        #[inline(always)]
        #[must_use]
        pub fn population(self) -> u8 {
            unsafe { self.0.count_ones().try_into().unwrap_unchecked() }
        }

        #[inline(always)]
        #[must_use]
        pub const fn and(self, other: Self) -> Self {
            Self::new_mask(self.0 & other.0)
        }

        #[inline(always)]
        #[must_use]
        pub fn pop(&mut self) -> Option<u8> {
            if self.is_empty() {
                None
            } else {
                let bit_index = unsafe { self.0.trailing_zeros().try_into().unwrap_unchecked() };
                self.0 &= self.0 - 1;
                Some(bit_index)
            }
        }

        #[inline(always)]
        pub fn set(&mut self, mask: BitVec) {
            self.0 |= mask.0;
        }

        #[inline(always)]
        pub fn clear(&mut self, mask: BitVec) {
            self.0 &= !mask.0;
        }
    }

    #[derive(Debug)]
    pub struct Board {
        rows: [BitVec; DIM],
        columns: [BitVec; DIM],
        boxes: [BitVec; DIM],
        occupied: [u8; DIM2],
    }

    impl Board {
        const EMPTY_CELL: u8 = b'.';

        #[inline(always)]
        #[must_use]
        pub const fn new() -> Self {
            Self {
                rows: [BitVec::ALL_SET; DIM],
                columns: [BitVec::ALL_SET; DIM],
                boxes: [BitVec::ALL_SET; DIM],
                occupied: [Self::EMPTY_CELL; DIM2],
            }
        }

        #[inline]
        pub fn read<U: Iterator<Item = Result<u8, std::io::Error>>>(bytes: &mut U) -> Result<Self, Option<std::io::Error>> {
            let mut board = Self::new();
            let mut coords = Coords::START;
            loop {
                if let Some(result) = bytes.next() {
                    match result {
                        Ok(byte) => {
                            if byte.is_ascii_whitespace() {
                                continue;
                            }
                            if byte != Self::EMPTY_CELL {
                                if !(b'1'..=b'9').contains(&byte) {
                                    return Err(None);
                                }
                                let value = byte - b'1';
                                let avail = board.available_values(coords);
                                if avail.is_none() || avail.is_some_and(|bv| bv.and(BitVec::new_bit(value)).is_empty()) {
                                    return Err(None);
                                }
                                board.occupy(coords, value);
                            }
                            if let Some(next) = coords.next() {
                                coords = next;
                            } else {
                                break;
                            }
                        }
                        Err(err) => return Err(Some(err)),
                    }
                } else {
                    return Err(None);
                }
            }
            Ok(board)
        }

        #[inline]
        pub fn print(&self) {
            for row in 0..(DIM as u32) {
                let mut coords = Coords::new(row, 0);
                let mut value = self.occupied[coords.i as usize];
                if value != Self::EMPTY_CELL {
                    value += b'1';
                }
                print!("{}", value as char);
                for column in 1..(DIM as u32) {
                    coords = Coords::new(row, column);
                    value = self.occupied[coords.i as usize];
                    if value != Self::EMPTY_CELL {
                        value += b'1';
                    }
                    print!(" {}", value as char);
                }
                println!();
            }
        }

        #[inline(always)]
        #[must_use]
        pub const fn available_values(&self, coords: Coords) -> Option<BitVec> {
            debug_assert!(coords.r < DIM as u32);
            debug_assert!(coords.c < DIM as u32);
            debug_assert!(coords.b < DIM as u32);
            debug_assert!(coords.i < DIM2 as u32);
            if unsafe { *self.occupied.as_ptr().add(coords.i as usize) } == Self::EMPTY_CELL {
                Some(
                    self.rows[coords.r as usize]
                        .and(self.columns[coords.c as usize])
                        .and(self.boxes[coords.b as usize]),
                )
            } else {
                None
            }
        }

        #[inline(always)]
        pub fn occupy(&mut self, coords: Coords, value: u8) {
            debug_assert!(coords.r < DIM as u32);
            debug_assert!(coords.c < DIM as u32);
            debug_assert!(coords.b < DIM as u32);
            debug_assert!(coords.i < DIM2 as u32);
            let mask = BitVec::new_bit(value);
            debug_assert_eq!(self.available_values(coords).unwrap().and(mask), mask);
            self.rows[coords.r as usize].clear(mask);
            self.columns[coords.c as usize].clear(mask);
            self.boxes[coords.b as usize].clear(mask);
            self.occupied[coords.i as usize] = value;
        }

        #[inline(always)]
        pub fn leave(&mut self, coords: Coords) {
            debug_assert!(coords.r < DIM as u32);
            debug_assert!(coords.c < DIM as u32);
            debug_assert!(coords.b < DIM as u32);
            debug_assert!(coords.i < DIM2 as u32);
            debug_assert_ne!(self.occupied[coords.i as usize], Self::EMPTY_CELL);
            let mask = BitVec::new_bit(self.occupied[coords.i as usize]);
            debug_assert_eq!(self.rows[coords.r as usize].and(mask), BitVec::new_mask(0));
            debug_assert_eq!(self.columns[coords.c as usize].and(mask), BitVec::new_mask(0));
            debug_assert_eq!(self.boxes[coords.b as usize].and(mask), BitVec::new_mask(0));
            self.rows[coords.r as usize].set(mask);
            self.columns[coords.c as usize].set(mask);
            self.boxes[coords.b as usize].set(mask);
            self.occupied[coords.i as usize] = Self::EMPTY_CELL;
        }
    }

    #[inline]
    pub fn solve_and<F: Fn(&Board)>(board: &mut Board, f: F) -> u128 {
        #[inline]
        fn solve<F: Fn(&Board)>(board: &mut Board, mut coords: Coords, f: &F) -> u128 {
            let mut solutions = 0;
            loop {
                if let Some(mut possibilities) = board.available_values(coords) {
                    while let Some(value) = possibilities.pop() {
                        board.occupy(coords, value);
                        solutions += solve(board, coords, f);
                        board.leave(coords);
                    }
                    break;
                } else if let Some(next) = coords.next() {
                    coords = next;
                } else {
                    f(board);
                    return 1;
                }
            }
            solutions
        }

        #[inline]
        fn solve_best<F: Fn(&Board)>(board: &mut Board, f: &F) -> u128 {
            let mut solutions = 0;
            let mut best_coords = Coords::START;
            let mut best_possibilities = BitVec::new_mask(0);
            let mut best_population = DIM as u8 + 1;
            let mut coords = Coords::START;
            let mut cells = 0;
            loop {
                if let Some(possibilities) = board.available_values(coords) {
                    let population = possibilities.population();
                    if population == 0 {
                        return solutions;
                    }
                    cells += 1;
                    if population < best_population {
                        best_coords = coords;
                        best_possibilities = possibilities;
                        best_population = population;
                        if best_population == 1 {
                            break;
                        }
                    }
                }
                if let Some(next) = coords.next() {
                    coords = next;
                } else {
                    break;
                }
            }
            if best_population == DIM as u8 + 1 {
                f(board);
                return 1;
            }
            if best_population > 1 && cells < BEST_THRESHOLD {
                while let Some(value) = best_possibilities.pop() {
                    board.occupy(best_coords, value);
                    solutions += solve(board, Coords::START, f);
                    board.leave(best_coords);
                }
            } else {
                while let Some(value) = best_possibilities.pop() {
                    board.occupy(best_coords, value);
                    solutions += solve_best(board, f);
                    board.leave(best_coords);
                }
            }
            solutions
        }

        solve_best(board, &f)
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        const TEST_COORDS: [(u8, u8, u8); 21] = [
            (0, 0, 0),
            (1, 3, 1),
            (2, 6, 2),
            (3, 1, 3),
            (4, 4, 4),
            (5, 7, 5),
            (6, 2, 6),
            (7, 5, 7),
            (0, 1, 1),
            (1, 4, 2),
            (2, 7, 3),
            (3, 2, 4),
            (4, 5, 5),
            (5, 8, 6),
            (6, 3, 8),
            (7, 6, 0),
            (0, 2, 2),
            (1, 5, 4),
            (2, 8, 1),
            (3, 3, 6),
            (4, 6, 7),
        ];
        const IMPROPERS: [(&str, u16); 10] = [
            (
                "1 2 3 . . . . . .\n\
                 . . . 2 3 5 . . .\n\
                 . . . . . . 3 4 2\n\
                 . 4 5 7 . . . . .\n\
                 . . . . 5 6 8 . .\n\
                 . . . . . . . 6 7\n\
                 . . 7 9 . . . . .\n\
                 . . . . . 8 1 . .\n\
                 . . . . . . . . .\n",
                13550,
            ),
            (".56.........2.......3576..........7......8.....8132....346.....8.....4..2.......8", 14582),
            ("1....7.9..3..2...8..96..5....52..9...1..8...26...............1.........7..7...3..", 18670),
            (".7.5...4......86...1.......3.....2.6...14.......7.....6.....8..8.2...............", 26948),
            ("1..92....524................5...81.2.........4.2....9..6...........3.945....71..6", 20640),
            ("48...251612..3..985........2.........................7........171..4..596952...74", 26030),
            ("9..87...4....3.....5...4..6.1....2.....123....8....6...6.9.7..1.........5..3.....", 27913),
            (".47..............1...59...6.3........58...73...2......5...29...8..15..........16.", 20049),
            ("8..........36......7..9.....5...7.......457.....1...3...1....68...5...1..9....4..", 28411),
            (".....1..4.......5......21.3.8.....3.......5264.1.....82..9.....8.6.5.....4.......", 24498),
        ];
        const PROPERS: [&str; 20] = [
            "..1..2...7..391.....2.8..933......8.......6....98...34....3...6..8..6.21...9..4..",
            ".3...5...7..6......68.2...3.....9..2..1...5..5..47..963...5.76...4..73.5...2...8.",
            "53..7....6..195....98....6.8...6...34..8.3..17...2...6.6....28....419..5....8..79",
            "8..........36......7..9.2...5...7.......457.....1...3...1....68..85...1..9....4..",
            "85....4.1......67...21....3..85....7...982...3....15..5....43...37......2.9....58",
            ".1.....2..3..9..1656..7...33.7..8..........89....6......6.254..9.5..1..7..3.....2",
            ".43.8.25.6.............1.949....4.7....6.8....1.2....382.5.............5.34.9.71.",
            "..3.2.6..9..3.5..1..18.64....81.29..7.......8..67.82....26.95..8..2.3..9..5.1.3..",
            "1..92....524.1...........7..5...81.2.........4.27...9..6...........3.945....71..6",
            "2...8.3...6..7..84.3.5..2.9...1.54.8.........4.27.6...3.1..7.4.72..4..6...4.1...3",
            "6..1.......93..4....3..9.58.6.....9..98256....3.....2...5..1.37..25..9..3..7.....",
            ".1....6.9..3.6...1.....8..393.24......4.8.9......37.523..7.....4...9.2..2.8....9.",
            "...6..7.13.......2.56.1.9...1..2.....934.71...6..3.....47.8.2..9.......8...5..3.7",
            ".56......1..2.......3576..........7.6....8.....8132....346.....867...4..2.......8",
            ".....12.4.......5....8.21.3.8.....3...3...5264.1.....82..9.....8.6.54....4528....",
            "...4.76.8...2.8.17...36.2...68........7...8.2.......6.6...74...8..9.2...3426.....",
            "..46..7..5..1..943..........965.8......7.4.8..289.3............8..4..397..98..5..",
            "1..4.5..3....8....53.1.9.67..1...8....93471...4..1..7............2...3..3.72.46.1",
            ".5.....174..2.............6....16.5.2.....4..3...8.....71.........8..3...........",
            ".7.5...4......86...1.......3.....2.6...14.......7.....6.....8..8.2..........7....",
        ];

        struct StrIter<'a>(std::str::Bytes<'a>);

        impl<'a> StrIter<'a> {
            #[inline(always)]
            #[must_use]
            fn new(str: &'a str) -> Self {
                Self(str.bytes())
            }
        }

        impl<'a> Iterator for StrIter<'a> {
            type Item = Result<u8, std::io::Error>;

            #[inline(always)]
            fn next(&mut self) -> Option<Self::Item> {
                Some(Ok(self.0.next()?))
            }
        }

        #[test]
        fn coords() {
            let mut prev: Option<Coords> = None;
            for row in 0..(DIM as u32) {
                for column in 0..(DIM as u32) {
                    let coords = Coords::new(row, column);
                    assert_eq!(coords.r, row);
                    assert_eq!(coords.c, column);
                    assert_eq!(coords.b, (row / ROOT as u32) * ROOT as u32 + (column / ROOT as u32));
                    assert_eq!(coords.i, row * DIM as u32 + column);
                    if let Some(p) = prev {
                        assert_eq!(p.next(), Some(coords));
                    }
                    prev.replace(coords);
                }
            }
            assert!(prev.is_some_and(|p| p.next().is_none()));
        }

        #[test]
        fn bitvec() {
            let mut v = BitVec::ALL_SET;
            for bit_index in 0..(DIM as u8) {
                let bv = BitVec::new_bit(bit_index);
                assert_eq!(bv.0, 1 << bit_index);
                assert_eq!(v.pop().unwrap(), bit_index);
            }
            assert!(BitVec::new_mask(0).is_empty());
            assert_eq!(BitVec::new_mask(0).population(), 0);
            for bits in 1..=BitVec::ALL_SET.0 {
                let bv = BitVec::new_mask(bits);
                assert_eq!(bv.0, bits);
                assert!(!bv.is_empty());
                assert_eq!(bv.population(), bits.count_ones() as u8);
            }
            for outer in 0..=BitVec::ALL_SET.0 {
                let ov = BitVec::new_mask(outer);
                assert_eq!(ov.0, outer);
                for inner in 0..=BitVec::ALL_SET.0 {
                    let iv = BitVec::new_mask(inner);
                    assert_eq!(ov.and(iv), BitVec::new_mask(outer & inner));
                    v = ov;
                    v.set(iv);
                    assert_eq!(v.0, outer | inner);
                    v = ov;
                    v.clear(iv);
                    assert_eq!(v.0, outer & !inner);
                }
            }
        }

        #[test]
        fn board() {
            type NaiveBoard = [[u8; DIM]; DIM];

            #[inline(always)]
            #[must_use]
            fn available_values(nb: &NaiveBoard, row: usize, column: usize) -> Option<BitVec> {
                if nb[row][column] != Board::EMPTY_CELL {
                    return None;
                }
                let mut avail = BitVec::ALL_SET;
                for c in 0..DIM {
                    let value = nb[row][c];
                    if value < DIM as u8 {
                        avail.clear(BitVec::new_bit(value));
                    }
                }
                for r in 0..DIM {
                    let value = nb[r][column];
                    if value < DIM as u8 {
                        avail.clear(BitVec::new_bit(value));
                    }
                }
                let row_ofs = (row / ROOT) * ROOT;
                let column_ofs = (column / ROOT) * ROOT;
                for r in row_ofs..(row_ofs + ROOT) {
                    for c in column_ofs..(column_ofs + ROOT) {
                        let value = nb[r][c];
                        if value < DIM as u8 {
                            avail.clear(BitVec::new_bit(value));
                        }
                    }
                }
                Some(avail)
            }

            fn check_board(nb: &NaiveBoard, b: &Board) {
                for r in 0..DIM {
                    for c in 0..DIM {
                        let coords = Coords::new(r as u32, c as u32);
                        assert_eq!(nb[r][c], b.occupied[coords.i as usize]);
                        assert_eq!(available_values(nb, r, c), b.available_values(coords));
                    }
                }
            }

            let mut nb = [[Board::EMPTY_CELL; DIM]; DIM];
            let mut b = Board::new();
            check_board(&nb, &b);
            for r in 0..DIM {
                for c in 0..DIM {
                    for v in 0..(DIM as u8) {
                        nb[r][c] = v;
                        let coords = Coords::new(r as u32, c as u32);
                        b.occupy(coords, v);
                        check_board(&nb, &b);
                        b.leave(coords);
                        nb[r][c] = Board::EMPTY_CELL;
                    }
                }
            }
            for (r, c, v) in TEST_COORDS {
                nb[r as usize][c as usize] = v;
                b.occupy(Coords::new(r as u32, c as u32), v);
                check_board(&nb, &b);
            }
            b = Board::read(&mut StrIter::new(IMPROPERS[0].0)).unwrap();
            check_board(&nb, &b);
        }

        #[test]
        fn solve() {
            let mut b; // = Board::new();
            for (str, solutions) in IMPROPERS {
                b = Board::read(&mut StrIter::new(str)).unwrap();
                assert_eq!(solve_and(&mut b, |_| ()), solutions as u128);
            }
            for str in PROPERS {
                b = Board::read(&mut StrIter::new(str)).unwrap();
                assert_eq!(solve_and(&mut b, |_| ()), 1);
            }
        }
    }
}

fn main() -> Result<(), std::io::Error> {
    use lib::*;
    use std::io::Read;

    let lock = std::io::stdin().lock();
    let mut iter = lock.bytes().peekable();
    while iter.peek().is_some() {
        match Board::read(&mut iter) {
            Ok(mut board) => {
                println!(
                    "solutions: {}",
                    solve_and(&mut board, |b| {
                        println!();
                        b.print();
                    })
                );
                while iter
                    .peek()
                    .is_some_and(|result| result.as_ref().is_ok_and(|&byte| byte.is_ascii_whitespace()))
                {
                    iter.next();
                }
            }
            Err(result) => match result {
                Some(err) => return Err(err),
                None => eprintln!("invalid sudoku!"),
            },
        }
    }
    Ok(())
}
