mod lib {
    #[derive(Debug, Clone, Copy)]
    pub struct Coords {
        r: u8,
        c: u8,
        b: u8,
        i: u8,
    }

    impl Coords {
        #[rustfmt::skip]
        const TOBOX: [u8; 9 * 9] = [
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
        pub const fn new(row: u8, column: u8) -> Self {
            Self::new_indexed(row, column, row * 9 + column)
        }

        #[inline(always)]
        #[must_use]
        const fn new_indexed(row: u8, column: u8, index: u8) -> Self {
            debug_assert!(row < 9 && column < 9 && index < 9 * 9);
            Self {
                r: row,
                c: column,
                b: Self::TOBOX[index as usize],
                i: index,
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
        #[inline(always)]
        #[must_use]
        pub const fn new(bit_mask: u16) -> Self {
            debug_assert!(bit_mask < 0x200);
            BitVec(bit_mask)
        }

        #[inline(always)]
        #[must_use]
        pub const fn new_bit(bit_index: u8) -> Self {
            debug_assert!(bit_index < 9);
            BitVec(1 << bit_index)
        }

        #[inline(always)]
        #[must_use]
        pub const fn is_empty(self) -> bool {
            self.0 == 0
        }

        #[inline(always)]
        #[must_use]
        pub const fn and(self, other: Self) -> Self {
            Self::new(self.0 & other.0)
        }

        #[inline(always)]
        #[must_use]
        pub fn front(self) -> u8 {
            debug_assert!(!self.is_empty());
            unsafe { self.0.trailing_zeros().try_into().unwrap_unchecked() }
        }

        #[inline(always)]
        pub fn pop(&mut self) {
            debug_assert!(!self.is_empty());
            self.0 &= self.0 - 1;
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
        rows: [BitVec; 9],
        columns: [BitVec; 9],
        boxes: [BitVec; 9],
        occupied: [u8; 9 * 9],
    }

    impl Board {
        const EMPTY: u8 = b'.';

        #[inline(always)]
        #[must_use]
        pub const fn new() -> Self {
            Self {
                rows: [BitVec(0x1ff); 9],
                columns: [BitVec(0x1ff); 9],
                boxes: [BitVec(0x1ff); 9],
                occupied: [Self::EMPTY; 9 * 9],
            }
        }

        #[inline(always)]
        #[must_use]
        pub fn read<U: Iterator<Item = Result<u8, std::io::Error>>>(bytes: &mut U) -> Result<Self, Option<std::io::Error>> {
            let mut board = Self::new();
            let mut coords = Coords::new(0, 0);
            loop {
                if let Some(res) = bytes.next() {
                    match res {
                        Ok(byte) => {
                            if byte.is_ascii_whitespace() {
                                continue;
                            }
                            if byte != Self::EMPTY {
                                if byte < b'1' || byte > b'9' {
                                    return Err(None);
                                }
                                let value = byte - b'1';
                                let avail = board.available_values(coords);
                                if avail.is_none() || avail.is_some_and(|bv| bv.and(BitVec::new_bit(value)).is_empty()) {
                                    return Err(None);
                                }
                                board.occupy(coords, value);
                            }
                            if let Some(c) = coords.next() {
                                coords = c;
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

        #[inline(always)]
        pub fn print(&self) {
            for row in 0..9 {
                let mut coords = Coords::new(row, 0);
                let mut value = self.occupied[coords.i as usize];
                if value != Self::EMPTY {
                    value += b'1';
                }
                print!("{}", value as char);
                for column in 1..9 {
                    coords = Coords::new(row, column);
                    value = self.occupied[coords.i as usize];
                    if value != Self::EMPTY {
                        value += b'1';
                    }
                    print!(" {}", value as char);
                }
                print!("\n");
            }
            print!("\n");
        }

        #[inline(always)]
        #[must_use]
        pub const fn available_values(&self, coords: Coords) -> Option<BitVec> {
            debug_assert!(coords.r < 9);
            debug_assert!(coords.c < 9);
            debug_assert!(coords.b < 9);
            debug_assert!(coords.i < 9 * 9);
            if self.occupied[coords.i as usize] == Self::EMPTY {
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
            debug_assert!(coords.r < 9);
            debug_assert!(coords.c < 9);
            debug_assert!(coords.b < 9);
            debug_assert!(coords.i < 9 * 9);
            let mask = BitVec::new_bit(value);
            debug_assert_eq!(self.available_values(coords).unwrap().and(mask), mask);
            self.rows[coords.r as usize].clear(mask);
            self.columns[coords.c as usize].clear(mask);
            self.boxes[coords.b as usize].clear(mask);
            self.occupied[coords.i as usize] = value;
        }

        #[inline(always)]
        pub fn leave(&mut self, coords: Coords, value: u8) {
            debug_assert!(coords.r < 9);
            debug_assert!(coords.c < 9);
            debug_assert!(coords.b < 9);
            debug_assert!(coords.i < 9 * 9);
            debug_assert_eq!(self.occupied[coords.i as usize], value);
            let mask = BitVec::new_bit(value);
            debug_assert_eq!(self.rows[coords.r as usize].and(mask), BitVec::new(0));
            debug_assert_eq!(self.columns[coords.c as usize].and(mask), BitVec::new(0));
            debug_assert_eq!(self.boxes[coords.b as usize].and(mask), BitVec::new(0));
            self.rows[coords.r as usize].set(mask);
            self.columns[coords.c as usize].set(mask);
            self.boxes[coords.b as usize].set(mask);
            self.occupied[coords.i as usize] = Self::EMPTY;
        }

        #[inline(never)]
        fn solve<F: Fn(&Self)>(&mut self, mut coords: Coords, f: &F) -> u128 {
            let mut result = 0;
            loop {
                if let Some(mut values) = self.available_values(coords) {
                    while !values.is_empty() {
                        let value = values.front();
                        self.occupy(coords, value);
                        result += self.solve(coords, f);
                        self.leave(coords, value);
                        values.pop();
                    }
                    break;
                } else if let Some(c) = coords.next() {
                    coords = c;
                } else {
                    f(&self);
                    return 1;
                }
            }
            result
        }

        #[inline(always)]
        pub fn solve_and<F: Fn(&Self)>(&mut self, f: F) -> u128 {
            self.solve(Coords::new(0, 0), &f)
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn coords() {
            let mut prev: Option<Coords> = None;
            for row in 0..9 {
                for column in 0..9 {
                    let coords = Coords::new(row, column);
                    assert_eq!(coords.r, row);
                    assert_eq!(coords.c, column);
                    assert_eq!(coords.b, (row / 3) * 3 + (column / 3));
                    assert_eq!(coords.i, row * 9 + column);
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
            let mut v = BitVec(0x1ff);
            for bit_index in 0..9 {
                assert_eq!(BitVec::new_bit(bit_index).0, 1 << bit_index);
                assert_eq!(v.front(), bit_index);
                v.pop();
            }
            assert!(BitVec::new(0).is_empty());
            for bits in 1..0x200 {
                let bv = BitVec::new(bits);
                assert_eq!(bv.0, bits);
                assert!(!bv.is_empty());
            }
            for outer in 0..0x200 {
                let ov = BitVec(outer);
                assert_eq!(ov.0, outer);
                for inner in 0..0x200 {
                    let iv = BitVec(inner);
                    assert_eq!(ov.and(iv), BitVec(outer & inner));
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

            type NaiveBoard = [[u8; 9]; 9];

            #[inline(always)]
            #[must_use]
            fn available_values(nb: &NaiveBoard, row: usize, column: usize) -> Option<BitVec> {
                if nb[row][column] != Board::EMPTY {
                    return None;
                }
                let mut avail = BitVec::new(0x1ff);
                for c in 0..9 {
                    let value = nb[row][c];
                    if value < 9 {
                        avail.clear(BitVec::new_bit(value));
                    }
                }
                for r in 0..9 {
                    let value = nb[r][column];
                    if value < 9 {
                        avail.clear(BitVec::new_bit(value));
                    }
                }
                let row_ofs = (row / 3) * 3;
                let column_ofs = (column / 3) * 3;
                for r in row_ofs..(row_ofs + 3) {
                    for c in column_ofs..(column_ofs + 3) {
                        let value = nb[r][c];
                        if value < 9 {
                            avail.clear(BitVec::new_bit(value));
                        }
                    }
                }
                Some(avail)
            }

            fn check_board(nb: &NaiveBoard, b: &Board) {
                for r in 0usize..9 {
                    for c in 0usize..9 {
                        let coords = Coords::new(r as u8, c as u8);
                        assert_eq!(nb[r][c], b.occupied[coords.i as usize]);
                        assert_eq!(available_values(nb, r, c), b.available_values(coords));
                    }
                }
            }

            let mut nb = [[Board::EMPTY; 9]; 9];
            let mut b = Board::new();
            check_board(&nb, &b);
            for r in 0..9 {
                for c in 0..9 {
                    for v in 0..9 {
                        nb[r][c] = v;
                        let coords = Coords::new(r as u8, c as u8);
                        b.occupy(coords, v);
                        check_board(&nb, &b);
                        b.leave(coords, v);
                        nb[r][c] = Board::EMPTY;
                    }
                }
            }
            for (r, c, v) in [
                (0, 0, 0),
                (1, 3, 1),
                (2, 6, 2),
                (3, 1, 3),
                (4, 4, 4),
                (5, 7, 5),
                (6, 2, 6),
                (7, 5, 7),
                (8, 8, 8),
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
            ] {
                nb[r][c] = v;
                b.occupy(Coords::new(r as u8, c as u8), v);
                check_board(&nb, &b);
            }
            let board_text: &str = "1 2 3 . . . . . .\n\
                                    . . . 2 3 5 . . .\n\
                                    . . . . . . 3 4 2\n\
                                    . 4 5 7 . . . . .\n\
                                    . . . . 5 6 8 . .\n\
                                    . . . . . . . 6 7\n\
                                    . . 7 9 . . . . .\n\
                                    . . . . . 8 1 . .\n\
                                    . . . . . . . . 9\n";
            b = Board::read(&mut StrIter::new(board_text)).unwrap();
            check_board(&nb, &b);
            assert_eq!(b.solve_and(|_| ()), 3827);
        }
    }
}

fn main() {
    use lib::*;
    use std::io::Read;

    let stdin = std::io::stdin();
    let lock = stdin.lock();
    let mut iter = lock.bytes().peekable();
    while iter.peek().is_some() {
        if let Ok(mut board) = Board::read(&mut iter) {
            println!("solutions: {}\n", board.solve_and(|b| b.print()));
            while iter
                .peek()
                .is_some_and(|result| result.as_ref().is_ok_and(|&byte| byte.is_ascii_whitespace()))
            {
                iter.next();
            }
        } else {
            eprintln!("io error or illegal sudoku format!");
        }
    }
}
