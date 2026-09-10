//@ [!lean] skip
use std::mem::discriminant;

pub enum EmptyEnum {}

#[derive(PartialEq)]
pub enum AlertLevel {
    Warning,
    Fatal,
}

#[derive(PartialEq)]
#[repr(u8)]
pub enum AlertLevelU8 {
    Warning = 1,
    Fatal = 2,
}

#[derive(PartialEq)]
#[repr(isize)]
pub enum SignedDiscr {
    NegThree = -3,
    NegTwo = -2,
    NegOne = -1,
    Zero = 0,
    PosOne = 1,
    PosTwo = 2,
    PosThree = 3,
}
