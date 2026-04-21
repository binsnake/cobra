//! Auto-generated 222 NPN-4 canonical-class expressions — DO NOT EDIT.
//! Source: lib/core/Npn4Table.inc (cobra-master).

use cobra_core::expr::Expr;

/// Return the canonical-form Boolean expression for NPN class `class_id`.
/// `var` maps a canonical variable index `0..=3` to the actual `Expr`
/// (possibly negated and re-permuted by the caller).
#[allow(clippy::too_many_lines, clippy::cognitive_complexity)]
pub fn build_npn4_canonical<F>(class_id: u8, var: F) -> Option<Box<Expr>>
where
    F: Fn(u32) -> Box<Expr>,
{
    let v = &var;
    Some(match class_id {
        1 => Expr::not(Expr::or(v(0), Expr::or(v(1), Expr::or(v(2), v(3))))),
        2 => Expr::not(Expr::or(v(1), Expr::or(v(2), v(3)))),
        3 => Expr::and(Expr::xor(v(0), v(1)), Expr::not(Expr::or(v(2), v(3)))),
        4 => Expr::not(Expr::or(v(2), Expr::or(v(3), Expr::and(v(0), v(1))))),
        5 => Expr::not(Expr::or(v(2), v(3))),
        6 => Expr::xor(
            v(3),
            Expr::or(
                v(3),
                Expr::xor(v(0), Expr::or(Expr::xor(v(1), v(2)), Expr::and(v(0), v(1)))),
            ),
        ),
        7 => Expr::not(Expr::or(
            v(3),
            Expr::xor(
                v(0),
                Expr::and(Expr::xor(v(0), v(2)), Expr::xor(v(0), v(1))),
            ),
        )),
        8 => Expr::xor(
            v(3),
            Expr::or(
                v(3),
                Expr::and(Expr::xor(v(1), v(2)), Expr::xor(v(0), v(2))),
            ),
        ),
        9 => Expr::not(Expr::or(
            v(3),
            Expr::or(Expr::xor(v(0), v(1)), Expr::and(v(0), v(2))),
        )),
        10 => Expr::not(Expr::or(
            v(3),
            Expr::xor(v(1), Expr::and(v(0), Expr::xor(v(1), v(2)))),
        )),
        11 => Expr::xor(v(3), Expr::or(v(3), Expr::xor(v(2), Expr::or(v(0), v(1))))),
        12 => Expr::not(Expr::or(v(3), Expr::and(v(2), Expr::or(v(0), v(1))))),
        13 => Expr::xor(v(3), Expr::or(v(3), Expr::xor(v(1), v(2)))),
        14 => Expr::not(Expr::or(
            v(3),
            Expr::xor(v(1), Expr::xor(v(2), Expr::or(v(0), Expr::or(v(1), v(2))))),
        )),
        15 => Expr::not(Expr::or(v(3), Expr::and(v(1), v(2)))),
        16 => Expr::not(Expr::or(v(3), Expr::xor(v(0), Expr::xor(v(1), v(2))))),
        17 => Expr::not(Expr::or(
            v(3),
            Expr::xor(v(1), Expr::xor(v(2), Expr::and(v(0), Expr::or(v(1), v(2))))),
        )),
        18 => Expr::not(Expr::or(
            v(3),
            Expr::and(v(2), Expr::not(Expr::xor(v(0), v(1)))),
        )),
        19 => Expr::xor(
            v(3),
            Expr::or(v(3), Expr::or(Expr::xor(v(0), v(2)), Expr::xor(v(0), v(1)))),
        ),
        20 => Expr::not(Expr::or(v(3), Expr::and(v(0), Expr::and(v(1), v(2))))),
        21 => Expr::not(v(3)),
        22 => Expr::xor(
            Expr::or(v(0), Expr::or(v(1), Expr::and(v(2), v(3)))),
            Expr::or(v(2), Expr::or(v(3), Expr::and(v(0), v(1)))),
        ),
        23 => Expr::not(Expr::xor(
            v(0),
            Expr::and(
                Expr::xor(v(0), Expr::or(v(1), v(2))),
                Expr::xor(v(0), Expr::or(v(3), Expr::and(v(1), v(2)))),
            ),
        )),
        24 => Expr::xor(
            v(2),
            Expr::or(
                Expr::and(v(2), Expr::or(v(0), v(1))),
                Expr::and(Expr::xor(v(1), v(3)), Expr::xor(v(0), v(3))),
            ),
        ),
        25 => Expr::not(Expr::or(
            Expr::xor(v(0), v(1)),
            Expr::xor(
                v(0),
                Expr::and(Expr::xor(v(0), v(3)), Expr::xor(v(0), v(2))),
            ),
        )),
        26 => Expr::and(
            Expr::or(v(0), Expr::xor(v(2), v(3))),
            Expr::xor(Expr::or(v(0), v(1)), Expr::or(v(2), v(3))),
        ),
        27 => Expr::not(Expr::xor(
            v(1),
            Expr::and(
                Expr::xor(v(1), Expr::or(v(2), v(3))),
                Expr::or(v(0), Expr::and(v(2), v(3))),
            ),
        )),
        28 => Expr::xor(
            v(2),
            Expr::or(Expr::and(v(2), v(3)), Expr::xor(v(3), Expr::or(v(0), v(1)))),
        ),
        29 => Expr::not(Expr::xor(
            v(2),
            Expr::and(Expr::xor(v(2), v(3)), Expr::xor(v(2), Expr::or(v(0), v(1)))),
        )),
        30 => Expr::and(
            Expr::xor(v(2), Expr::or(v(1), v(3))),
            Expr::xor(v(3), Expr::or(v(0), v(1))),
        ),
        31 => Expr::not(Expr::or(
            Expr::and(v(2), v(3)),
            Expr::xor(
                v(0),
                Expr::xor(v(2), Expr::and(v(1), Expr::xor(v(0), v(3)))),
            ),
        )),
        32 => Expr::not(Expr::xor(
            v(2),
            Expr::and(
                Expr::or(v(0), v(1)),
                Expr::xor(v(2), Expr::or(v(3), Expr::and(v(1), v(2)))),
            ),
        )),
        33 => Expr::xor(
            v(3),
            Expr::or(Expr::xor(v(1), v(2)), Expr::and(v(3), Expr::or(v(0), v(1)))),
        ),
        34 => Expr::xor(
            v(3),
            Expr::or(
                Expr::xor(v(1), v(2)),
                Expr::not(Expr::xor(v(3), Expr::or(v(0), v(1)))),
            ),
        ),
        35 => Expr::xor(
            Expr::or(v(0), Expr::or(v(1), v(2))),
            Expr::or(v(3), Expr::and(v(1), v(2))),
        ),
        36 => Expr::not(Expr::or(
            Expr::and(v(1), v(2)),
            Expr::and(v(3), Expr::or(v(0), Expr::or(v(1), v(2)))),
        )),
        37 => Expr::xor(
            Expr::or(v(0), Expr::or(v(1), v(2))),
            Expr::or(v(3), Expr::xor(v(0), Expr::xor(v(1), v(2)))),
        ),
        38 => Expr::not(Expr::or(
            Expr::xor(v(0), Expr::xor(v(1), v(2))),
            Expr::and(v(3), Expr::or(v(0), v(1))),
        )),
        39 => Expr::xor(
            v(0),
            Expr::or(
                Expr::and(v(0), v(3)),
                Expr::and(Expr::xor(v(2), v(3)), Expr::xor(v(1), v(3))),
            ),
        ),
        40 => Expr::xor(
            v(3),
            Expr::or(
                Expr::xor(v(0), Expr::and(v(1), v(2))),
                Expr::not(Expr::xor(v(3), Expr::or(v(1), v(2)))),
            ),
        ),
        41 => Expr::xor(
            v(3),
            Expr::or(
                Expr::xor(v(0), v(1)),
                Expr::xor(v(0), Expr::and(v(2), Expr::xor(v(0), v(3)))),
            ),
        ),
        42 => Expr::not(Expr::xor(
            v(2),
            Expr::and(
                Expr::xor(v(2), v(3)),
                Expr::or(Expr::xor(v(0), v(1)), Expr::and(v(0), v(3))),
            ),
        )),
        43 => Expr::xor(
            v(3),
            Expr::or(
                Expr::xor(v(0), v(1)),
                Expr::or(Expr::xor(v(0), v(2)), Expr::and(v(0), v(3))),
            ),
        ),
        44 => Expr::not(Expr::xor(
            v(0),
            Expr::and(
                Expr::xor(v(0), v(3)),
                Expr::or(Expr::xor(v(0), v(2)), Expr::xor(v(0), v(1))),
            ),
        )),
        45 => Expr::and(
            Expr::xor(v(0), v(3)),
            Expr::and(Expr::xor(v(2), v(3)), Expr::xor(v(1), v(3))),
        ),
        46 => Expr::not(Expr::or(
            Expr::xor(v(0), v(1)),
            Expr::or(Expr::xor(v(0), v(2)), Expr::and(v(0), v(3))),
        )),
        47 => Expr::and(
            Expr::xor(v(0), v(3)),
            Expr::not(Expr::or(Expr::xor(v(1), v(2)), Expr::and(v(1), v(3)))),
        ),
        48 => Expr::not(Expr::or(
            Expr::xor(v(1), v(2)),
            Expr::xor(v(1), Expr::and(v(0), Expr::xor(v(1), v(3)))),
        )),
        49 => Expr::xor(
            Expr::or(v(0), Expr::or(v(1), v(2))),
            Expr::or(v(3), Expr::xor(v(2), Expr::and(v(0), v(1)))),
        ),
        50 => Expr::not(Expr::or(
            Expr::xor(v(2), Expr::and(v(0), v(1))),
            Expr::and(v(3), Expr::or(v(0), v(1))),
        )),
        51 => Expr::not(Expr::or(
            Expr::xor(v(0), v(1)),
            Expr::xor(v(2), Expr::and(v(0), Expr::xor(v(2), v(3)))),
        )),
        52 => Expr::not(Expr::or(
            Expr::and(v(0), v(3)),
            Expr::xor(v(0), Expr::or(v(1), Expr::xor(v(0), v(2)))),
        )),
        53 => Expr::not(Expr::or(
            Expr::and(v(3), Expr::or(v(0), v(1))),
            Expr::and(v(2), Expr::not(Expr::and(v(0), v(1)))),
        )),
        54 => Expr::xor(
            v(3),
            Expr::or(
                Expr::xor(v(0), Expr::xor(v(1), v(2))),
                Expr::and(v(3), Expr::or(v(0), v(1))),
            ),
        ),
        55 => Expr::xor(
            v(3),
            Expr::or(
                Expr::xor(v(0), Expr::xor(v(1), v(2))),
                Expr::not(Expr::xor(v(3), Expr::or(v(0), v(1)))),
            ),
        ),
        56 => Expr::xor(
            Expr::or(v(0), Expr::or(v(1), v(2))),
            Expr::or(v(3), Expr::xor(v(0), v(1))),
        ),
        57 => Expr::not(Expr::or(
            Expr::xor(v(0), v(1)),
            Expr::and(v(3), Expr::or(v(0), v(2))),
        )),
        58 => Expr::xor(
            v(0),
            Expr::or(
                Expr::and(v(0), v(3)),
                Expr::xor(v(1), Expr::or(v(1), Expr::xor(v(2), v(3)))),
            ),
        ),
        59 => Expr::not(Expr::xor(
            v(3),
            Expr::and(
                Expr::xor(v(3), Expr::or(v(1), v(2))),
                Expr::xor(v(0), Expr::or(v(1), v(3))),
            ),
        )),
        60 => Expr::xor(
            Expr::or(v(0), Expr::or(v(1), v(2))),
            Expr::or(v(3), Expr::and(v(2), Expr::xor(v(0), v(1)))),
        ),
        61 => Expr::not(Expr::and(
            Expr::or(v(2), v(3)),
            Expr::or(Expr::xor(v(0), v(1)), Expr::and(v(3), Expr::or(v(0), v(2)))),
        )),
        62 => Expr::and(Expr::xor(v(0), v(3)), Expr::xor(v(3), Expr::or(v(1), v(2)))),
        63 => Expr::not(Expr::or(
            Expr::and(v(0), v(3)),
            Expr::xor(v(0), Expr::or(v(1), v(2))),
        )),
        64 => Expr::xor(v(3), Expr::or(v(0), Expr::and(v(3), Expr::or(v(1), v(2))))),
        65 => Expr::xor(
            v(3),
            Expr::or(v(0), Expr::not(Expr::xor(v(3), Expr::or(v(1), v(2))))),
        ),
        66 => Expr::xor(
            v(0),
            Expr::or(
                Expr::and(v(0), v(3)),
                Expr::xor(v(2), Expr::or(v(2), Expr::xor(v(0), Expr::xor(v(1), v(3))))),
            ),
        ),
        67 => Expr::not(Expr::or(
            Expr::and(v(0), v(3)),
            Expr::xor(v(0), Expr::or(v(2), Expr::and(v(1), Expr::or(v(0), v(3))))),
        )),
        68 => Expr::xor(
            v(3),
            Expr::or(
                v(0),
                Expr::xor(v(1), Expr::and(v(2), Expr::xor(v(1), v(3)))),
            ),
        ),
        69 => Expr::not(Expr::xor(
            v(2),
            Expr::and(Expr::xor(v(2), v(3)), Expr::or(v(0), Expr::and(v(1), v(3)))),
        )),
        70 => Expr::and(
            Expr::xor(v(3), Expr::or(v(1), v(2))),
            Expr::xor(v(3), Expr::or(v(0), Expr::xor(v(1), v(2)))),
        ),
        71 => Expr::not(Expr::or(
            Expr::and(v(3), Expr::or(v(1), v(2))),
            Expr::and(Expr::xor(v(0), v(2)), Expr::xor(v(0), v(1))),
        )),
        72 => Expr::xor(
            v(3),
            Expr::or(v(0), Expr::or(Expr::xor(v(1), v(2)), Expr::and(v(1), v(3)))),
        ),
        73 => Expr::not(Expr::xor(
            v(1),
            Expr::and(Expr::xor(v(1), v(3)), Expr::or(v(0), Expr::xor(v(1), v(2)))),
        )),
        74 => Expr::and(
            Expr::xor(v(3), Expr::or(v(0), v(1))),
            Expr::xor(v(3), Expr::or(v(2), Expr::and(v(0), v(1)))),
        ),
        75 => Expr::not(Expr::or(
            Expr::and(v(0), v(3)),
            Expr::xor(
                v(0),
                Expr::or(Expr::xor(v(1), v(2)), Expr::and(v(1), Expr::or(v(0), v(3)))),
            ),
        )),
        76 => Expr::and(
            Expr::xor(v(3), Expr::or(v(0), v(1))),
            Expr::or(v(0), Expr::xor(v(2), v(3))),
        ),
        77 => Expr::not(Expr::or(
            Expr::and(v(3), Expr::or(v(0), v(1))),
            Expr::xor(v(0), Expr::or(v(0), Expr::xor(v(1), v(2)))),
        )),
        78 => Expr::xor(v(3), Expr::or(v(0), Expr::or(v(1), Expr::and(v(2), v(3))))),
        79 => Expr::not(Expr::xor(
            v(2),
            Expr::and(Expr::xor(v(2), v(3)), Expr::or(v(0), v(1))),
        )),
        80 => Expr::xor(v(3), Expr::or(v(0), Expr::or(v(1), v(2)))),
        81 => Expr::xor(v(1), Expr::or(Expr::xor(v(2), v(3)), Expr::and(v(1), v(2)))),
        82 => Expr::xor(
            Expr::or(v(1), Expr::and(v(2), v(3))),
            Expr::or(v(2), Expr::or(v(3), Expr::not(Expr::or(v(0), v(1))))),
        ),
        83 => Expr::not(Expr::xor(
            v(1),
            Expr::and(Expr::xor(v(1), v(3)), Expr::xor(v(1), v(2))),
        )),
        84 => Expr::xor(Expr::or(v(1), v(2)), Expr::or(v(0), v(3))),
        85 => Expr::not(Expr::and(Expr::or(v(1), v(2)), Expr::or(v(0), v(3)))),
        86 => Expr::xor(
            v(2),
            Expr::and(Expr::or(v(0), v(3)), Expr::or(v(2), Expr::xor(v(1), v(3)))),
        ),
        87 => Expr::xor(
            Expr::or(v(0), v(3)),
            Expr::or(v(2), Expr::not(Expr::xor(v(1), v(3)))),
        ),
        88 => Expr::xor(Expr::or(v(0), v(3)), Expr::or(v(2), Expr::and(v(1), v(3)))),
        89 => Expr::not(Expr::and(
            Expr::or(v(1), v(2)),
            Expr::or(v(3), Expr::not(Expr::xor(v(0), v(2)))),
        )),
        90 => Expr::xor(
            Expr::or(v(0), v(3)),
            Expr::or(v(2), Expr::and(v(1), Expr::or(v(3), Expr::not(v(0))))),
        ),
        91 => Expr::not(Expr::or(
            Expr::and(v(0), v(2)),
            Expr::and(v(3), Expr::or(v(1), v(2))),
        )),
        92 => Expr::xor(
            v(3),
            Expr::and(
                Expr::or(v(1), v(2)),
                Expr::or(v(3), Expr::xor(v(0), Expr::and(v(1), v(2)))),
            ),
        ),
        93 => Expr::xor(
            v(1),
            Expr::or(
                Expr::and(v(1), v(3)),
                Expr::xor(v(2), Expr::or(v(3), Expr::not(v(0)))),
            ),
        ),
        94 => Expr::xor(
            Expr::or(v(1), v(2)),
            Expr::or(v(3), Expr::xor(v(0), Expr::xor(v(1), v(2)))),
        ),
        95 => Expr::not(Expr::and(
            Expr::or(v(1), v(2)),
            Expr::or(v(3), Expr::xor(v(0), Expr::xor(v(1), v(2)))),
        )),
        96 => Expr::xor(
            v(3),
            Expr::or(
                Expr::and(v(2), v(3)),
                Expr::xor(v(1), Expr::and(v(0), v(2))),
            ),
        ),
        97 => Expr::not(Expr::xor(
            v(2),
            Expr::xor(
                v(3),
                Expr::and(
                    Expr::or(v(2), Expr::not(v(1))),
                    Expr::or(v(3), Expr::xor(v(0), v(1))),
                ),
            ),
        )),
        98 => Expr::xor(
            v(1),
            Expr::and(
                Expr::or(v(0), v(3)),
                Expr::not(Expr::and(Expr::xor(v(1), v(3)), Expr::xor(v(1), v(2)))),
            ),
        ),
        99 => Expr::not(Expr::xor(
            v(2),
            Expr::and(
                Expr::xor(v(2), v(3)),
                Expr::xor(v(1), Expr::and(v(0), v(2))),
            ),
        )),
        100 => Expr::xor(
            Expr::or(v(1), v(2)),
            Expr::or(v(3), Expr::and(v(0), Expr::and(v(1), v(2)))),
        ),
        101 => Expr::xor(
            v(3),
            Expr::or(
                Expr::xor(v(1), v(2)),
                Expr::not(Expr::xor(v(1), Expr::or(v(3), Expr::xor(v(0), v(1))))),
            ),
        ),
        102 => Expr::xor(
            v(3),
            Expr::or(
                Expr::xor(v(1), v(2)),
                Expr::xor(v(0), Expr::xor(v(1), Expr::and(v(0), v(3)))),
            ),
        ),
        103 => Expr::and(Expr::xor(v(2), v(3)), Expr::xor(v(1), v(3))),
        104 => Expr::not(Expr::or(
            Expr::xor(v(1), v(2)),
            Expr::xor(v(1), Expr::xor(v(3), Expr::or(v(0), Expr::or(v(1), v(3))))),
        )),
        105 => Expr::not(Expr::or(Expr::xor(v(1), v(2)), Expr::and(v(1), v(3)))),
        106 => Expr::xor(
            Expr::or(v(1), v(2)),
            Expr::or(v(3), Expr::xor(v(1), Expr::or(v(2), Expr::not(v(0))))),
        ),
        107 => Expr::xor(
            v(1),
            Expr::and(
                Expr::or(v(0), v(3)),
                Expr::or(Expr::not(v(2)), Expr::and(v(1), v(3))),
            ),
        ),
        108 => Expr::not(Expr::or(
            Expr::and(v(1), v(3)),
            Expr::xor(v(2), Expr::and(v(1), Expr::or(v(0), v(2)))),
        )),
        109 => Expr::not(Expr::xor(v(2), Expr::and(v(1), Expr::xor(v(2), v(3))))),
        110 => Expr::xor(
            Expr::or(v(1), v(2)),
            Expr::or(v(3), Expr::and(v(0), Expr::xor(v(1), v(2)))),
        ),
        111 => Expr::or(
            Expr::not(Expr::or(v(0), v(3))),
            Expr::and(Expr::xor(v(2), v(3)), Expr::xor(v(1), v(3))),
        ),
        112 => Expr::xor(
            Expr::or(v(1), v(2)),
            Expr::or(v(3), Expr::and(v(0), Expr::not(Expr::and(v(1), v(2))))),
        ),
        113 => Expr::not(Expr::and(
            Expr::or(v(0), v(3)),
            Expr::or(Expr::xor(v(1), v(2)), Expr::and(v(1), v(3))),
        )),
        114 => Expr::xor(
            Expr::or(v(1), v(2)),
            Expr::or(
                v(3),
                Expr::and(Expr::xor(v(1), v(2)), Expr::xor(v(0), v(1))),
            ),
        ),
        115 => Expr::not(Expr::xor(
            v(1),
            Expr::or(
                Expr::and(v(0), Expr::not(v(3))),
                Expr::and(v(2), Expr::xor(v(1), v(3))),
            ),
        )),
        116 => Expr::not(Expr::xor(
            v(3),
            Expr::and(
                Expr::xor(v(1), Expr::or(v(0), v(3))),
                Expr::xor(v(1), Expr::xor(v(2), v(3))),
            ),
        )),
        117 => Expr::xor(
            v(3),
            Expr::or(v(1), Expr::and(v(2), Expr::or(v(3), Expr::not(v(0))))),
        ),
        118 => Expr::xor(
            v(3),
            Expr::or(
                v(1),
                Expr::not(Expr::xor(v(2), Expr::or(v(3), Expr::xor(v(0), v(2))))),
            ),
        ),
        119 => Expr::xor(
            v(3),
            Expr::or(
                v(1),
                Expr::xor(v(0), Expr::xor(v(2), Expr::and(v(0), v(3)))),
            ),
        ),
        120 => Expr::xor(v(3), Expr::or(v(1), v(2))),
        121 => Expr::and(Expr::xor(v(2), v(3)), Expr::xor(v(0), v(1))),
        122 => Expr::not(Expr::xor(
            v(0),
            Expr::xor(
                Expr::or(v(1), v(2)),
                Expr::and(Expr::or(v(1), v(3)), Expr::or(v(0), Expr::xor(v(2), v(3)))),
            ),
        )),
        123 => Expr::xor(
            v(0),
            Expr::and(
                Expr::or(v(0), Expr::xor(v(2), v(3))),
                Expr::or(v(1), Expr::and(v(2), v(3))),
            ),
        ),
        124 => Expr::xor(
            Expr::or(v(1), Expr::and(v(2), v(3))),
            Expr::or(v(0), Expr::not(Expr::xor(v(2), v(3)))),
        ),
        125 => Expr::and(Expr::xor(v(0), v(1)), Expr::not(Expr::and(v(2), v(3)))),
        126 => Expr::not(Expr::or(
            Expr::and(v(0), v(1)),
            Expr::xor(
                v(2),
                Expr::and(
                    Expr::xor(v(2), v(3)),
                    Expr::xor(v(0), Expr::xor(v(1), v(3))),
                ),
            ),
        )),
        127 => Expr::not(Expr::xor(
            v(2),
            Expr::xor(v(3), Expr::or(Expr::xor(v(0), v(1)), Expr::and(v(2), v(3)))),
        )),
        128 => Expr::not(Expr::xor(
            v(0),
            Expr::xor(
                v(1),
                Expr::or(
                    Expr::xor(v(2), v(3)),
                    Expr::xor(v(0), Expr::xor(v(2), Expr::and(v(1), Expr::or(v(0), v(2))))),
                ),
            ),
        )),
        129 => Expr::not(Expr::xor(
            v(2),
            Expr::and(
                Expr::xor(v(2), v(3)),
                Expr::xor(v(0), Expr::xor(v(1), v(3))),
            ),
        )),
        130 => Expr::xor(
            Expr::or(v(0), v(2)),
            Expr::or(Expr::and(v(0), v(1)), Expr::and(v(3), Expr::or(v(1), v(2)))),
        ),
        131 => Expr::or(
            Expr::not(Expr::or(v(1), v(3))),
            Expr::and(Expr::xor(v(2), v(3)), Expr::xor(v(0), v(1))),
        ),
        132 => Expr::xor(
            Expr::or(v(0), Expr::or(v(1), v(2))),
            Expr::or(Expr::and(v(0), v(1)), Expr::and(v(2), v(3))),
        ),
        133 => Expr::xor(
            v(2),
            Expr::xor(
                Expr::and(v(0), v(1)),
                Expr::and(v(3), Expr::or(Expr::xor(v(0), v(2)), Expr::xor(v(0), v(1)))),
            ),
        ),
        134 => Expr::xor(
            Expr::or(v(2), Expr::not(Expr::xor(v(0), v(1)))),
            Expr::or(v(3), Expr::and(v(0), Expr::and(v(1), v(2)))),
        ),
        135 => Expr::xor(
            v(0),
            Expr::or(
                Expr::and(v(1), Expr::xor(v(2), v(3))),
                Expr::and(v(2), Expr::not(Expr::xor(v(0), v(3)))),
            ),
        ),
        136 => Expr::not(Expr::xor(
            v(3),
            Expr::and(
                Expr::xor(v(1), Expr::and(v(0), v(3))),
                Expr::xor(v(0), Expr::xor(v(1), v(2))),
            ),
        )),
        137 => Expr::xor(
            v(3),
            Expr::or(
                Expr::xor(v(2), Expr::and(v(0), v(1))),
                Expr::xor(v(0), Expr::xor(v(1), v(3))),
            ),
        ),
        138 => Expr::and(
            Expr::xor(v(2), v(3)),
            Expr::xor(v(0), Expr::xor(v(1), v(2))),
        ),
        139 => Expr::not(Expr::or(
            Expr::and(v(2), v(3)),
            Expr::or(
                Expr::and(v(0), Expr::xor(v(1), v(2))),
                Expr::xor(v(0), Expr::xor(v(1), v(3))),
            ),
        )),
        140 => Expr::not(Expr::xor(
            Expr::or(v(1), v(3)),
            Expr::and(
                Expr::xor(v(2), v(3)),
                Expr::xor(v(0), Expr::and(v(1), v(3))),
            ),
        )),
        141 => Expr::xor(v(2), Expr::or(Expr::xor(v(0), v(1)), Expr::and(v(2), v(3)))),
        142 => Expr::not(Expr::or(
            Expr::and(v(0), Expr::xor(v(1), v(2))),
            Expr::xor(
                v(3),
                Expr::and(Expr::xor(v(2), v(3)), Expr::xor(v(0), v(1))),
            ),
        )),
        143 => Expr::not(Expr::xor(
            v(3),
            Expr::and(Expr::xor(v(2), v(3)), Expr::xor(v(0), v(1))),
        )),
        144 => Expr::and(
            Expr::xor(v(2), v(3)),
            Expr::xor(v(0), Expr::xor(v(2), Expr::or(v(1), Expr::and(v(0), v(2))))),
        ),
        145 => Expr::xor(
            Expr::or(v(2), Expr::not(Expr::xor(v(0), v(1)))),
            Expr::or(v(3), Expr::and(v(1), Expr::xor(v(0), v(2)))),
        ),
        146 => Expr::xor(
            v(2),
            Expr::xor(
                v(3),
                Expr::and(
                    Expr::xor(v(2), Expr::or(v(0), v(3))),
                    Expr::xor(v(0), Expr::xor(v(1), v(3))),
                ),
            ),
        ),
        147 => Expr::xor(
            v(3),
            Expr::or(
                Expr::and(v(2), Expr::or(v(0), v(3))),
                Expr::not(Expr::xor(v(1), Expr::and(v(0), v(3)))),
            ),
        ),
        148 => Expr::xor(
            v(2),
            Expr::and(
                Expr::or(v(1), v(3)),
                Expr::or(Expr::xor(v(0), v(1)), Expr::and(v(2), v(3))),
            ),
        ),
        149 => Expr::not(Expr::xor(
            v(0),
            Expr::xor(
                v(3),
                Expr::or(
                    Expr::and(v(0), v(2)),
                    Expr::and(v(1), Expr::xor(v(2), v(3))),
                ),
            ),
        )),
        150 => Expr::xor(
            v(2),
            Expr::or(
                Expr::and(v(2), v(3)),
                Expr::xor(v(0), Expr::or(v(1), Expr::and(v(0), v(2)))),
            ),
        ),
        151 => Expr::not(Expr::xor(
            v(3),
            Expr::and(
                Expr::xor(v(2), Expr::or(v(0), v(3))),
                Expr::xor(v(1), Expr::and(v(0), v(3))),
            ),
        )),
        152 => Expr::xor(
            v(3),
            Expr::or(
                Expr::not(Expr::xor(v(0), v(1))),
                Expr::and(v(2), Expr::or(v(0), v(3))),
            ),
        ),
        153 => Expr::not(Expr::xor(
            v(3),
            Expr::and(Expr::xor(v(0), v(1)), Expr::xor(v(2), Expr::or(v(0), v(3)))),
        )),
        154 => Expr::xor(v(2), Expr::and(v(3), Expr::or(v(2), Expr::xor(v(0), v(1))))),
        155 => Expr::xor(
            v(3),
            Expr::or(
                v(2),
                Expr::not(Expr::xor(
                    v(0),
                    Expr::and(v(1), Expr::or(v(3), Expr::not(v(0)))),
                )),
            ),
        ),
        156 => Expr::xor(
            v(3),
            Expr::or(
                v(2),
                Expr::xor(v(0), Expr::xor(v(3), Expr::and(v(1), Expr::or(v(0), v(3))))),
            ),
        ),
        157 => Expr::xor(v(3), Expr::or(v(2), Expr::xor(v(0), Expr::xor(v(1), v(3))))),
        158 => Expr::xor(v(3), Expr::or(v(2), Expr::not(Expr::xor(v(0), v(1))))),
        159 => Expr::xor(
            Expr::or(Expr::and(v(0), v(1)), Expr::and(v(2), v(3))),
            Expr::or(v(0), Expr::or(v(1), Expr::or(v(2), v(3)))),
        ),
        160 => Expr::xor(
            v(2),
            Expr::or(
                Expr::and(v(2), v(3)),
                Expr::xor(v(3), Expr::and(v(0), v(1))),
            ),
        ),
        161 => Expr::not(Expr::or(
            Expr::and(v(2), v(3)),
            Expr::xor(
                v(0),
                Expr::xor(v(1), Expr::and(Expr::or(v(0), v(1)), Expr::or(v(2), v(3)))),
            ),
        )),
        162 => Expr::xor(
            v(0),
            Expr::and(
                Expr::or(v(2), v(3)),
                Expr::or(
                    Expr::and(v(0), v(1)),
                    Expr::xor(v(0), Expr::xor(v(2), v(3))),
                ),
            ),
        ),
        163 => Expr::and(
            Expr::not(Expr::and(v(2), v(3))),
            Expr::or(Expr::xor(v(0), v(1)), Expr::xor(v(0), Expr::or(v(2), v(3)))),
        ),
        164 => Expr::and(
            Expr::xor(v(2), v(3)),
            Expr::not(Expr::and(v(1), Expr::xor(v(0), v(2)))),
        ),
        165 => Expr::not(Expr::or(
            Expr::and(v(2), v(3)),
            Expr::xor(
                v(1),
                Expr::and(
                    Expr::xor(v(0), v(3)),
                    Expr::xor(v(0), Expr::xor(v(1), v(2))),
                ),
            ),
        )),
        166 => Expr::xor(
            v(2),
            Expr::or(
                Expr::and(v(2), v(3)),
                Expr::xor(v(0), Expr::or(v(1), Expr::xor(v(0), v(3)))),
            ),
        ),
        167 => Expr::not(Expr::or(
            Expr::and(v(2), v(3)),
            Expr::and(Expr::xor(v(0), v(2)), Expr::or(v(1), Expr::xor(v(0), v(3)))),
        )),
        168 => Expr::xor(
            Expr::or(v(2), Expr::and(v(0), v(1))),
            Expr::or(v(3), Expr::xor(v(2), Expr::or(v(0), Expr::xor(v(1), v(2))))),
        ),
        169 => Expr::xor(
            v(2),
            Expr::xor(
                Expr::or(v(1), v(3)),
                Expr::and(v(0), Expr::and(v(1), Expr::xor(v(2), v(3)))),
            ),
        ),
        170 => Expr::and(
            Expr::xor(v(2), v(3)),
            Expr::or(Expr::xor(v(0), v(3)), Expr::xor(v(0), v(1))),
        ),
        171 => Expr::xor(
            v(2),
            Expr::or(
                Expr::not(Expr::or(v(0), v(1))),
                Expr::and(v(3), Expr::or(v(2), Expr::xor(v(0), v(1)))),
            ),
        ),
        172 => Expr::xor(
            Expr::or(v(0), v(3)),
            Expr::or(
                Expr::and(v(2), v(3)),
                Expr::and(v(1), Expr::xor(v(0), v(2))),
            ),
        ),
        173 => Expr::xor(
            Expr::and(v(1), v(3)),
            Expr::or(
                Expr::and(v(0), Expr::xor(v(2), v(3))),
                Expr::not(Expr::xor(v(1), v(2))),
            ),
        ),
        174 => Expr::xor(
            Expr::or(v(2), Expr::and(v(0), v(1))),
            Expr::or(v(3), Expr::xor(v(2), Expr::or(v(0), v(1)))),
        ),
        175 => Expr::xor(
            Expr::or(v(2), Expr::and(v(0), v(1))),
            Expr::or(v(3), Expr::not(Expr::or(v(0), v(1)))),
        ),
        176 => Expr::xor(v(3), Expr::or(v(2), Expr::and(v(0), Expr::and(v(1), v(3))))),
        177 => Expr::xor(
            v(3),
            Expr::or(
                v(2),
                Expr::not(Expr::or(Expr::xor(v(0), v(3)), Expr::xor(v(0), v(1)))),
            ),
        ),
        178 => Expr::xor(
            v(3),
            Expr::or(v(2), Expr::and(v(0), Expr::not(Expr::xor(v(1), v(3))))),
        ),
        179 => Expr::xor(v(3), Expr::or(v(2), Expr::and(v(0), v(1)))),
        180 => Expr::xor(v(2), v(3)),
        181 => Expr::and(
            Expr::xor(Expr::or(v(0), v(1)), Expr::and(v(2), v(3))),
            Expr::xor(Expr::and(v(0), v(1)), Expr::or(v(2), v(3))),
        ),
        182 => Expr::not(Expr::xor(
            v(0),
            Expr::xor(
                v(1),
                Expr::or(
                    Expr::xor(v(2), v(3)),
                    Expr::and(v(0), Expr::and(v(1), v(2))),
                ),
            ),
        )),
        183 => Expr::xor(
            v(0),
            Expr::and(
                Expr::or(v(1), v(2)),
                Expr::or(
                    Expr::and(v(0), v(3)),
                    Expr::xor(v(3), Expr::and(v(1), v(2))),
                ),
            ),
        ),
        184 => Expr::not(Expr::xor(
            v(0),
            Expr::xor(
                v(1),
                Expr::or(
                    Expr::xor(v(2), v(3)),
                    Expr::and(v(0), Expr::not(Expr::xor(v(1), v(2)))),
                ),
            ),
        )),
        185 => Expr::xor(
            v(0),
            Expr::xor(
                v(1),
                Expr::xor(
                    Expr::or(v(2), v(3)),
                    Expr::or(Expr::xor(v(2), v(3)), Expr::and(v(0), v(1))),
                ),
            ),
        ),
        186 => Expr::xor(
            v(0),
            Expr::and(
                Expr::or(v(1), v(2)),
                Expr::not(Expr::and(
                    Expr::xor(v(0), v(3)),
                    Expr::xor(v(0), Expr::and(v(1), v(2))),
                )),
            ),
        ),
        187 => Expr::not(Expr::or(
            Expr::xor(v(0), Expr::xor(v(3), Expr::or(v(1), v(2)))),
            Expr::xor(v(0), Expr::xor(v(1), Expr::xor(v(2), Expr::or(v(0), v(3))))),
        )),
        188 => Expr::not(Expr::xor(
            Expr::or(v(1), v(2)),
            Expr::and(
                Expr::xor(v(0), v(3)),
                Expr::xor(v(3), Expr::and(v(1), v(2))),
            ),
        )),
        189 => Expr::xor(
            v(0),
            Expr::xor(
                v(1),
                Expr::and(v(2), Expr::or(Expr::xor(v(0), v(3)), Expr::xor(v(0), v(1)))),
            ),
        ),
        190 => Expr::not(Expr::or(
            Expr::and(v(0), Expr::xor(v(1), v(2))),
            Expr::xor(
                v(2),
                Expr::and(Expr::xor(v(1), v(3)), Expr::xor(v(0), v(3))),
            ),
        )),
        191 => Expr::not(Expr::or(
            Expr::and(v(2), Expr::xor(v(0), v(1))),
            Expr::xor(v(0), Expr::xor(v(3), Expr::or(v(1), v(2)))),
        )),
        192 => Expr::not(Expr::xor(
            Expr::or(v(1), v(2)),
            Expr::and(
                Expr::xor(v(0), v(3)),
                Expr::xor(v(3), Expr::and(v(1), Expr::or(v(0), v(2)))),
            ),
        )),
        193 => Expr::xor(
            v(0),
            Expr::and(
                Expr::or(v(3), Expr::xor(v(0), v(1))),
                Expr::or(Expr::xor(v(1), v(2)), Expr::and(v(0), v(1))),
            ),
        ),
        194 => Expr::xor(
            v(0),
            Expr::or(
                Expr::xor(v(1), v(2)),
                Expr::and(v(0), Expr::and(v(1), v(3))),
            ),
        ),
        195 => Expr::xor(
            v(0),
            Expr::or(
                Expr::xor(v(1), v(2)),
                Expr::not(Expr::or(Expr::xor(v(0), v(3)), Expr::xor(v(0), v(1)))),
            ),
        ),
        196 => Expr::xor(
            v(0),
            Expr::and(
                Expr::or(v(0), Expr::xor(v(1), v(2))),
                Expr::not(Expr::xor(v(3), Expr::or(v(1), Expr::and(v(2), v(3))))),
            ),
        ),
        197 => Expr::not(Expr::xor(
            v(0),
            Expr::xor(
                v(1),
                Expr::and(v(3), Expr::or(Expr::not(v(2)), Expr::and(v(0), v(1)))),
            ),
        )),
        198 => Expr::xor(
            Expr::or(v(0), v(2)),
            Expr::or(
                Expr::and(v(1), v(3)),
                Expr::and(v(2), Expr::xor(v(0), v(1))),
            ),
        ),
        199 => Expr::xor(
            v(1),
            Expr::xor(
                Expr::or(v(2), Expr::not(v(3))),
                Expr::and(v(0), Expr::or(Expr::xor(v(1), v(3)), Expr::xor(v(1), v(2)))),
            ),
        ),
        200 => Expr::xor(
            v(0),
            Expr::xor(
                v(1),
                Expr::xor(v(3), Expr::or(Expr::xor(v(2), v(3)), Expr::and(v(0), v(1)))),
            ),
        ),
        201 => Expr::not(Expr::xor(
            v(3),
            Expr::xor(
                Expr::or(v(1), v(2)),
                Expr::or(v(0), Expr::and(v(1), Expr::and(v(2), v(3)))),
            ),
        )),
        202 => Expr::xor(
            v(1),
            Expr::or(
                Expr::and(v(3), Expr::xor(v(0), v(2))),
                Expr::and(v(2), Expr::xor(v(0), Expr::xor(v(1), v(3)))),
            ),
        ),
        203 => Expr::not(Expr::xor(
            v(0),
            Expr::xor(
                v(3),
                Expr::or(
                    Expr::and(v(0), v(1)),
                    Expr::xor(v(2), Expr::and(v(1), v(3))),
                ),
            ),
        )),
        204 => Expr::xor(
            v(1),
            Expr::xor(
                v(2),
                Expr::and(v(0), Expr::xor(v(3), Expr::and(v(1), v(2)))),
            ),
        ),
        205 => Expr::not(Expr::xor(
            v(0),
            Expr::xor(v(3), Expr::or(Expr::xor(v(1), v(2)), Expr::and(v(0), v(1)))),
        )),
        206 => Expr::xor(
            Expr::and(v(0), v(1)),
            Expr::or(
                Expr::xor(v(2), v(3)),
                Expr::xor(v(0), Expr::xor(v(1), v(2))),
            ),
        ),
        207 => Expr::xor(
            v(2),
            Expr::or(
                Expr::xor(v(0), v(1)),
                Expr::xor(v(0), Expr::xor(v(2), v(3))),
            ),
        ),
        208 => Expr::xor(
            v(0),
            Expr::or(
                Expr::xor(v(1), v(2)),
                Expr::and(v(3), Expr::not(Expr::xor(v(0), v(1)))),
            ),
        ),
        209 => Expr::xor(
            v(3),
            Expr::or(
                Expr::and(v(0), v(1)),
                Expr::and(v(2), Expr::not(Expr::xor(v(0), Expr::xor(v(1), v(3))))),
            ),
        ),
        210 => Expr::xor(
            v(0),
            Expr::xor(
                v(3),
                Expr::and(
                    Expr::xor(v(2), Expr::and(v(0), v(3))),
                    Expr::xor(v(1), Expr::xor(v(2), v(3))),
                ),
            ),
        ),
        211 => Expr::xor(
            v(1),
            Expr::xor(
                v(3),
                Expr::and(
                    Expr::xor(v(0), v(1)),
                    Expr::xor(v(2), Expr::and(v(1), v(3))),
                ),
            ),
        ),
        212 => Expr::xor(
            v(0),
            Expr::xor(
                v(3),
                Expr::and(Expr::xor(v(0), v(2)), Expr::xor(v(0), v(1))),
            ),
        ),
        213 => Expr::not(Expr::xor(
            v(3),
            Expr::and(Expr::xor(v(1), v(2)), Expr::xor(v(0), v(2))),
        )),
        214 => Expr::not(Expr::xor(
            v(2),
            Expr::xor(
                Expr::or(v(0), v(1)),
                Expr::and(v(3), Expr::or(v(2), Expr::and(v(0), v(1)))),
            ),
        )),
        215 => Expr::not(Expr::xor(
            v(2),
            Expr::xor(
                Expr::or(v(1), Expr::and(v(0), v(2))),
                Expr::and(v(3), Expr::or(v(0), v(2))),
            ),
        )),
        216 => Expr::xor(v(3), Expr::or(Expr::xor(v(0), v(1)), Expr::and(v(0), v(2)))),
        217 => Expr::xor(
            v(0),
            Expr::xor(v(1), Expr::or(Expr::xor(v(1), v(2)), Expr::xor(v(0), v(3)))),
        ),
        218 => Expr::xor(
            v(1),
            Expr::xor(v(3), Expr::and(v(0), Expr::xor(v(1), v(2)))),
        ),
        219 => Expr::not(Expr::xor(v(2), Expr::xor(v(3), Expr::or(v(0), v(1))))),
        220 => Expr::not(Expr::xor(v(1), Expr::xor(v(2), v(3)))),
        221 => Expr::xor(v(0), Expr::xor(v(1), Expr::xor(v(2), v(3)))),
        _ => return None,
    })
}
