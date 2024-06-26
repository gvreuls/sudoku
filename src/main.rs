mod lib {
    const ROOT: usize = 3;
    const DIM: usize = ROOT * ROOT;
    const DIM2: usize = DIM * DIM;
    const BEST_THRESHOLD_MAX: u32 = ((DIM - 1) * (ROOT + 1)) as u32;
    const BEST_THRESHOLD_MIN: u32 = (DIM + DIM - 1) as u32;

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
    pub struct BitVec(u32);

    impl BitVec {
        pub const ALL_CLEAR: Self = Self(0);
        pub const ALL_SET: Self = Self((1 << DIM) - 1);

        #[inline(always)]
        #[must_use]
        pub const fn new_mask(bit_mask: u32) -> Self {
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
            self.0.count_ones() as u8
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
                let bit_index = self.0.trailing_zeros() as u8;
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
                                let possibilities = board.available_values(coords);
                                if possibilities.is_none()
                                    || possibilities.is_some_and(|values| values.and(BitVec::new_bit(value)).is_empty())
                                {
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
        #[allow(clippy::write_with_newline)]
        pub fn write<T: std::io::Write>(&self, buffer: &mut T, pretty: bool) -> std::io::Result<()> {
            for row in 0..(DIM as u32) {
                let mut coords = Coords::new(row, 0);
                let mut value = self.occupied[coords.i as usize];
                if value != Self::EMPTY_CELL {
                    value += b'1';
                }
                write!(buffer, "{}", value as char)?;
                for column in 1..(DIM as u32) {
                    coords = Coords::new(row, column);
                    value = self.occupied[coords.i as usize];
                    if value != Self::EMPTY_CELL {
                        value += b'1';
                    }
                    if pretty {
                        write!(buffer, " ")?;
                    }
                    write!(buffer, "{}", value as char)?;
                }
                if pretty {
                    write!(buffer, "\n")?;
                }
            }
            Ok(())
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
            debug_assert_eq!(self.rows[coords.r as usize].and(mask), BitVec::ALL_CLEAR);
            debug_assert_eq!(self.columns[coords.c as usize].and(mask), BitVec::ALL_CLEAR);
            debug_assert_eq!(self.boxes[coords.b as usize].and(mask), BitVec::ALL_CLEAR);
            self.rows[coords.r as usize].set(mask);
            self.columns[coords.c as usize].set(mask);
            self.boxes[coords.b as usize].set(mask);
            self.occupied[coords.i as usize] = Self::EMPTY_CELL;
        }
    }

    #[inline]
    pub fn solve_and<F: FnMut(&Board) -> std::io::Result<()>>(board: &mut Board, mut f: F) -> std::io::Result<u128> {
        #[inline]
        fn solve<F: FnMut(&Board) -> std::io::Result<()>>(
            board: &mut Board, mut coords: Coords, f: &mut F,
        ) -> std::io::Result<u128> {
            let mut solutions = 0;
            loop {
                if let Some(mut possibilities) = board.available_values(coords) {
                    while let Some(value) = possibilities.pop() {
                        board.occupy(coords, value);
                        solutions += solve(board, coords, f)?;
                        board.leave(coords);
                    }
                    break;
                } else if let Some(next) = coords.next() {
                    coords = next;
                } else {
                    f(board)?;
                    solutions = 1;
                    break;
                }
            }
            Ok(solutions)
        }

        #[inline]
        fn solve_best<F: FnMut(&Board) -> std::io::Result<()>>(
            board: &mut Board, mut best_threshold: u32, f: &mut F,
        ) -> std::io::Result<u128> {
            let mut solutions = 0;
            let mut best_coords = Coords::START;
            let mut best_possibilities = BitVec::ALL_CLEAR;
            let mut best_population = DIM as u8 + 1;
            let mut empty_cells = 0;
            let mut coords = Coords::START;
            loop {
                if let Some(possibilities) = board.available_values(coords) {
                    let population = possibilities.population();
                    if population == 0 {
                        return Ok(solutions);
                    }
                    empty_cells += 1;
                    if population < best_population {
                        best_coords = coords;
                        best_possibilities = possibilities;
                        best_population = population;
                        if best_population == 1 {
                            if best_threshold > BEST_THRESHOLD_MIN {
                                best_threshold -= 1;
                            }
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
                f(board)?;
                return Ok(1);
            }
            if best_population > 1 && empty_cells < best_threshold {
                while let Some(value) = best_possibilities.pop() {
                    board.occupy(best_coords, value);
                    solutions += solve(board, Coords::START, f)?;
                    board.leave(best_coords);
                }
            } else {
                while let Some(value) = best_possibilities.pop() {
                    board.occupy(best_coords, value);
                    solutions += solve_best(board, best_threshold, f)?;
                    board.leave(best_coords);
                }
            }
            Ok(solutions)
        }

        solve_best(board, BEST_THRESHOLD_MAX, &mut f)
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
        const IMPROPERS: [(&str, u16); 5] = [
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
            (".47..............1...59...6.3........58...73...2......5...29...8..15..........16.", 20049),
            (".....5.8....6.1.43..........1.5........1.6...3.......553.....61........4.........", 0),
        ];
        const PROPERS: [&str; 25] = [
            ".5.....174..2.............6....16.5.2.....4..3...8.....71.........8..3...........",
            ".7.5...4......86...1.......3.....2.6...14.......7.....6.....8..8.2..........7....",
            ".3.89.1........2.....5.........12..........578........14.......9.2.........3...6.",
            "4..7............87.......3.6.....5......13.......2.4.....5.42...31.......8.......",
            "....4....12.....73.3...8.....4...6.....2.3.....5........6.9.5...7.....2..........",
            "....4..2..5.9......1..........8..1.52...3..........9..49...2...3......6....1.....",
            "...8.1..........435............7.8........1...2..3....6......75..34........2..6..",
            "...7.....1...........43.2..........6...5.9.........418....81.....2....5..4....3..",
            "...95...1..3...4.....8...........21.85...7...9..........2..3............1......85",
            ".......1......2..3...4...........5..4.16.......71......5....2......8..4..3.91....",
            ".......814..3.....3...5....19....5......82......6......82....5....7..4...........",
            ".......15.2..6..........4.8..3...9.....1..........8...15.4.........7.3..8......6.",
            ".482............6..2.......9...67.........1.8....3....6.9....7....1..2..3........",
            "...1...4.57.......3........6..25..........17...........814...........3.2....7.5..",
            ".8.4.........7.2........1...3.....89....25........4...2.7...5.....9...6.1........",
            "..71.53........2.....9.........2.7.461............3......6...1.2...8....8........",
            "..8...1.......2.5.6...7.....1.....2....36.......4......5.1..4..7.....6..........7",
            "5...4..6........12....1.....2.8...........49.......7..7..3..8.....2.6...4........",
            "....183......7..5..4.....2..2.5...........6..........7...6..24.7..3.....1........",
            ".41.........3..5.....2.....2..5..3......4..6.8.........6..1..4.37....2...........",
            "...1.2..8.3.7.....4........5...4.6..6......2....8.........964...81...............",
            "6..3.1.........8........4..3..5...1.2...4.....8.........91....7.4..2...........6.",
            "1...67....4.....5.............53..2...54.....72.......8.....6.7...2...........1..",
            "456..........9.2..............5.1...3.....9.....6........47...6.39....5.2........",
            ".27...5.....5.1....3...........7.2..8..6..............6.4.....81......6..5..2....",
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
            assert!(BitVec::ALL_CLEAR.is_empty());
            assert_eq!(BitVec::ALL_CLEAR.population(), 0);
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
            fn available_values(naive_board: &NaiveBoard, row: usize, column: usize) -> Option<BitVec> {
                if naive_board[row][column] != Board::EMPTY_CELL {
                    return None;
                }
                let mut avail = BitVec::ALL_SET;
                for c in 0..DIM {
                    let value = naive_board[row][c];
                    if value < DIM as u8 {
                        avail.clear(BitVec::new_bit(value));
                    }
                }
                for r in 0..DIM {
                    let value = naive_board[r][column];
                    if value < DIM as u8 {
                        avail.clear(BitVec::new_bit(value));
                    }
                }
                let row_ofs = (row / ROOT) * ROOT;
                let column_ofs = (column / ROOT) * ROOT;
                for r in row_ofs..(row_ofs + ROOT) {
                    for c in column_ofs..(column_ofs + ROOT) {
                        let value = naive_board[r][c];
                        if value < DIM as u8 {
                            avail.clear(BitVec::new_bit(value));
                        }
                    }
                }
                Some(avail)
            }

            fn check_board(naive_board: &NaiveBoard, board: &Board) {
                for row in 0..DIM {
                    for column in 0..DIM {
                        let coords = Coords::new(row as u32, column as u32);
                        assert_eq!(naive_board[row][column], board.occupied[coords.i as usize]);
                        assert_eq!(available_values(naive_board, row, column), board.available_values(coords));
                    }
                }
            }

            let mut naive_board = [[Board::EMPTY_CELL; DIM]; DIM];
            let mut board = Board::new();
            check_board(&naive_board, &board);
            for row in 0..DIM {
                for column in 0..DIM {
                    for value in 0..(DIM as u8) {
                        naive_board[row][column] = value;
                        let coords = Coords::new(row as u32, column as u32);
                        board.occupy(coords, value);
                        check_board(&naive_board, &board);
                        board.leave(coords);
                        naive_board[row][column] = Board::EMPTY_CELL;
                    }
                }
            }
            for (row, column, value) in TEST_COORDS {
                naive_board[row as usize][column as usize] = value;
                board.occupy(Coords::new(row as u32, column as u32), value);
                check_board(&naive_board, &board);
            }
            board = Board::read(&mut StrIter::new(IMPROPERS[0].0)).unwrap();
            check_board(&naive_board, &board);
        }

        #[test]
        fn solve() {
            let mut board;
            for (str, solutions) in IMPROPERS {
                board = Board::read(&mut StrIter::new(str)).unwrap();
                assert_eq!(solve_and(&mut board, |_| Ok(())).unwrap(), solutions as u128);
            }
            for str in PROPERS {
                board = Board::read(&mut StrIter::new(str)).unwrap();
                assert_eq!(solve_and(&mut board, |_| Ok(())).unwrap(), 1);
            }
        }
    }
}

#[inline(always)]
#[allow(clippy::write_with_newline)]
fn filter_solve(stdout: &std::io::Stdout, stderr: &std::io::Stderr, pretty_print: bool) -> std::io::Result<()> {
    use lib::*;
    use std::io::{Read, Write};

    let mut iter = std::io::stdin().lock().bytes().peekable();
    let mut first_sudoku = true;
    while iter.peek().is_some() {
        match Board::read(&mut iter) {
            Ok(mut board) => {
                let solutions = solve_and(&mut board, |b| {
                    let mut olock = stdout.lock();
                    if first_sudoku {
                        first_sudoku = false;
                    } else {
                        write!(olock, "\n")?;
                    }
                    b.write(&mut olock, pretty_print)
                })?;
                let mut olock = stdout.lock();
                if !(first_sudoku || pretty_print) {
                    write!(olock, "\n")?;
                }
                writeln!(olock, "solutions: {}", solutions)?;
                while iter
                    .peek()
                    .is_some_and(|result| result.as_ref().is_ok_and(|&byte| byte.is_ascii_whitespace()))
                {
                    iter.next();
                }
            }
            Err(result) => match result {
                Some(err) => return Err(err),
                None => writeln!(stderr.lock(), "invalid sudoku!")?,
            },
        }
    }
    Ok(())
}

#[inline(always)]
fn print_help(stdout: &std::io::Stdout) -> std::io::Result<()> {
    use std::io::Write;

    const NAME: &str = env!("CARGO_PKG_NAME");
    const VERSION: &str = env!("CARGO_PKG_VERSION");
    const DESCRIPTION: &str = env!("CARGO_PKG_DESCRIPTION");
    let authors = env!("CARGO_PKG_AUTHORS").replace(':', ", ");
    writeln!(
        stdout.lock(),
        "{NAME} v{VERSION} by {authors}.\n  {DESCRIPTION}\n\
         USAGE:\n  \
           {NAME} [OPTIONS] < input_file [> output_file]\n\
         OPTIONS:\n  \
           -h, --help\tPrints this text and exits.\n  \
           -r, --raw\tPrints solutions without whitespace.\n\
         FILE FORMAT:\n  \
           * Sudokus consist of 81 cell characters optionally separated by whitespace.\n  \
           * Valid cell characters are '1' through '9' and '.' indicating an empty cell.\n  \
           * Files can contain multiple sudokus."
    )
}

fn main() -> std::io::Result<()> {
    use std::io::Write;

    let stdout = std::io::stdout();
    let stderr = std::io::stderr();
    let mut help = false;
    let mut pretty_print = true;
    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "-r" | "--raw" => pretty_print = false,
            "-h" | "--help" => help = true,
            _ => writeln!(stderr.lock(), "ignoring illegal argument '{}'!", arg)?,
        }
    }
    if help {
        print_help(&stdout)
    } else {
        filter_solve(&stdout, &stderr, pretty_print)
    }
}
