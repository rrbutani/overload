// #![recursion_limit = "1024"]

// #![feature(fn_traits)]
// #![feature(unboxed_closures)]
// #![feature(trace_macros)]

// #[macro_use]
// extern crate eager;

// use eager::{eager, eager_macro_rules};

// use std::ops::{Add, FnOnce, FnMut, Fn};

// #[derive(Debug, Clone, Copy)]
// struct Adder<T: Copy>(T);

// macro_rules! adder_func {
//     (($($idents:ident),+):($($tys:ident),+)) => {
//         adder_func_inner! {
//             ($($idents),+):($($tys),+)
//             BOUNDS(adder_func_triangle!(LAST(_T) $($tys)*))
//         }
//     };
// }

// macro_rules! adder_func_triangle {
//     (LAST($last:ty) $ty:ident $($tys:ident)*) => {
//         $ty: Add<$last>,
//         adder_func_triangle!(LAST(<$ty as Add<$last>>::Output) $($tys)*)
//     };
//     (LAST($last:ty)) => { }
// }

// macro_rules! adder_func_last {
//     (LAST($last:ty) $ty:ident $($tys:ident)*) => {
//         // $ty: Add<$last>,
//         adder_func_last!(LAST(<$ty as Add<$last>>::Output) $($tys)*)
//     };
//     (LAST($last:ty)) => { $last }
// }

// macro_rules! adder_func_inner {
//     (($($idents:ident),+):($($tys:ident),+) BOUNDS($($bounds:tt)*)) => {
//         impl<_T, $($tys),+> FnOnce<($($tys,)+)> for Adder<_T>
//         where
//             _T: Copy,
//             // adder_func_triangle!(LAST(_T) $($tys)*),
//             $($bounds)*
//         {
//             type Output = adder_func_last!(LAST(_T) $($tys)*);
//             extern "rust-call" fn call_once(self, ($($idents,)*): ($($tys,)+)) -> Self::Output {
//                 self.0 $(+ $idents)+
//             }
//         }
//         // impl<A, B, C> where A: Add<T>, B: Add<<A as Add<T>>::Output>, C: Add<B as Add<<A as Add<T>>::Output>::Output>

//         // impl<T: Copy + Add<T>> FnOnce<(T,)> for Adder<T> {
//         //     type Output = <T as Add<T>>::Output;
//         //     extern "rust-call" fn call_once(self, (a,): (T,)) -> Self::Output {
//         //         self.0 + a
//         //     }
//         // }

//         // impl<T: Copy + Add<T>> FnMut<(T,)> for Adder<T> {
//         //     extern "rust-call" fn call_mut(&mut self, (a,): (T,)) -> Self::Output {
//         //         self.0 + a
//         //     }
//         // }

//         // impl<T: Copy + Add<T>> Fn<(T,)> for Adder<T> {
//         //     extern "rust-call" fn call(&self, (a,): (T,)) -> Self::Output {
//         //         self.0 + a
//         //     }
//         // }
//     };
// }

// macro_rules! adder_func {
//     (($($idents:ident),+):($($tys:ident),+)) => {
//         adder_func_inner! {
//             ($($idents),+):($($tys),+)
//             BOUNDS(adder_func_triangle!(LAST(_T) $($tys)*))
//         }
//     };
// }

// macro_rules! adder_func_triangle {
//     (LAST($last:ty) $ty:ident $($tys:ident)*) => {
//         $ty: Add<$last>,
//         adder_func_triangle!(LAST(<$ty as Add<$last>>::Output) $($tys)*)
//     };
//     (LAST($last:ty)) => { }
// }

// // macro_rules! bound {
// //     (LAST($last:ty) $p:ident $()) => {};
// // }

// macro_rules! adder_func_last {
//     (LAST($last:ty) $ty:ident $($tys:ident)*) => {
//         adder_func_last!(LAST(<$ty as Add<$last>>::Output) $($tys)*)
//     };
//     (LAST($last:ty)) => { $last }
// }

// macro_rules! adder_func {
//     (($($idents:ident),+):($($ty:ident $($following:ident)*),+)) => {
//         impl<_T, $($ty),+> FnOnce<($($ty,)+)> for Adder<_T>
//         where
//             _T: Copy,
//             $($ty: adder_func_last!(LAST(_T) $ty $($following)*))*,
//             // adder_func_triangle!(LAST(_T) $($tys)*),
//             // $($bounds)*
//         {
//             type Output = adder_func_last!(LAST(_T) $($ty)*);
//             extern "rust-call" fn call_once(self, ($($idents,)*): ($($ty,)+)) -> Self::Output {
//                 self.0 $(+ $idents)+
//             }
//         }
//     };
// }


// eager_macro_rules!{ $eager_1
//     macro_rules! adder_func_triangle {
//         (LAST($last:ty) $ty:ident $($tys:ident)*) => {
//             $ty: Add<$last>,
//             adder_func_triangle!(LAST(<$ty as Add<$last>>::Output) $($tys)*)
//         };
//         (LAST($last:ty)) => { }
//     }

//     macro_rules! adder_func {
//         (($($idents:ident),+):($($tys:ident),+)) => {
//             adder_func_inner! {
//                 ($($idents),+):($($tys),+)
//                 BOUNDS(adder_func_triangle!(LAST(_T) $($tys)*))
//             }
//        };
//     }
// }

// macro_rules! adder_func_last {
//     (LAST($last:ty) $ty:ident $($tys:ident)*) => {
//         // $ty: Add<$last>,
//         adder_func_last!(LAST(<$ty as Add<$last>>::Output) $($tys)*)
//     };
//     (LAST($last:ty)) => { $last }
// }

// macro_rules! adder_func_inner {
//     (($($idents:ident),+):($($tys:ident),+) BOUNDS($($bounds:tt)*)) => {
//         impl<_T, $($tys),+> FnOnce<($($tys,)+)> for Adder<_T>
//         where
//             _T: Copy,
//             // adder_func_triangle!(LAST(_T) $($tys)*),
//             $($bounds)*
//         {
//             type Output = adder_func_last!(LAST(_T) $($tys)*);
//             extern "rust-call" fn call_once(self, ($($idents,)*): ($($tys,)+)) -> Self::Output {
//                 self.0 $(+ $idents)+
//             }
//         }
//     };
// }

// trace_macros!(true);

// // adder_func_inner!{(a, b, c): (A, B, C) BOUNDS(
// //     A: Add<_T>,
// //     A: Add<B>,
// // )}

// eager! { lazy! { adder_func_inner!{(a, b, c): (A, B, C) BOUNDS(eager! { adder_func_triangle!(LAST(_T) A B C)}) } }}
// trace_macros!(false);

// eager_macro_rules!{ $eager_1
//     macro_rules! adder_func_triangle {
//         (LAST($last:ty) $ty:ident $($tys:ident)*) => {
//             $ty: Add<$last>,
//             adder_func_triangle!(LAST(<$ty as Add<$last>>::Output) $($tys)*)
//         };
//         (LAST($last:ty)) => { }
//     }

//     macro_rules! adder_func {
//         (($($idents:ident),+):($($tys:ident),+)) => {
//             adder_func_inner! {
//                 ($($idents),+):($($tys),+)
//                 BOUNDS(adder_func_triangle!(LAST(_T) $($tys)*))
//             }
//        };
//     }
// }

// macro_rules! adder_func_last {
//     (LAST($last:ty) $ty:ident $($tys:ident)*) => {
//         // $ty: Add<$last>,
//         adder_func_last!(LAST(<$ty as Add<$last>>::Output) $($tys)*)
//     };
//     (LAST($last:ty)) => { $last }
// }

// macro_rules! adder_func_inner {
//     (($($idents:ident),+):($($tys:ident),+) BOUNDS($($bounds:tt)*)) => {
//         impl<_T, $($tys),+> FnOnce<($($tys,)+)> for Adder<_T>
//         where
//             _T: Copy,
//             // adder_func_triangle!(LAST(_T) $($tys)*),
//             $($bounds)*
//         {
//             type Output = adder_func_last!(LAST(_T) $($tys)*);
//             extern "rust-call" fn call_once(self, ($($idents,)*): ($($tys,)+)) -> Self::Output {
//                 self.0 $(+ $idents)+
//             }
//         }
//     };
// }

// macro_rules! right_recursive {
//     ({$a:expr} {$b:expr} $({$rest:expr})*) => {
//         right_recursive! { (($b) + ($a)) $({$rest})* }
//     };

//     ({$e:expr}) => { ($e) }
// }

// trace_macros!(true);

// // adder_func_inner!{(a, b, c): (A, B, C) BOUNDS(
// //     A: Add<_T>,
// //     A: Add<B>,
// // )}

// eager! { lazy! { adder_func_inner!{(a, b, c): (A, B, C) BOUNDS(eager! { adder_func_triangle!(LAST(_T) A B C)}) } }}
// trace_macros!(false);

// eager_macro_rules!{ $eager_1
//     macro_rules! adder_func_triangle {
//         (LAST($last:ty) $ty:ident $($tys:ident)*) => {
//             $ty: Add<$last>,
//             adder_func_triangle!(LAST(<$ty as Add<$last>>::Output) $($tys)*)
//         };
//         (LAST($last:ty)) => { }
//     }

//     macro_rules! adder_func {
//         (($($idents:ident),+):($($tys:ident),+)) => {
//             adder_func_inner! {
//                 ($($idents),+):($($tys),+)
//                 BOUNDS(adder_func_triangle!(LAST(_T) $($tys)*))
//             }
//        };
//     }
// }

// macro_rules! adder_func_last {
//     (LAST($last:ty) $ty:ident $($tys:ident)*) => {
//         // $ty: Add<$last>,
//         adder_func_last!(LAST(<$ty as Add<$last>>::Output) $($tys)*)
//     };
//     (LAST($last:ty)) => { $last }
// }

// macro_rules! adder_func_inner {
//     (($($idents:ident),+):($($tys:ident),+) BOUNDS($($bounds:tt)*)) => {
//         impl<_T, $($tys),+> FnOnce<($($tys,)+)> for Adder<_T>
//         where
//             _T: Copy,
//             // adder_func_triangle!(LAST(_T) $($tys)*),
//             $($bounds)*
//         {
//             type Output = adder_func_last!(LAST(_T) $($tys)*);
//             extern "rust-call" fn call_once(self, ($($idents,)*): ($($tys,)+)) -> Self::Output {
//                 right_recursive!({self.0} $({$idents})*)
//             }
//         }
//     };
// }

// macro_rules! right_recursive {
//     ({$a:expr} {$b:expr} $({$rest:expr})*) => {
//         right_recursive! { { (($b) + ($a)) } $({$rest})* }
//     };

//     ({$e:expr}) => { ($e) }
// }

// // trace_macros!(true);

// // adder_func_inner!{(a, b, c): (A, B, C) BOUNDS(
// //     A: Add<_T>,
// //     A: Add<B>,
// // )}

// eager! { lazy! { adder_func_inner!{(a, b, c): (A, B, C) BOUNDS(eager! { adder_func_triangle!(LAST(_T) A B C)}) } }}
// trace_macros!(false);

////////////////////////////////////////////////////////////////////////////////////////

// impl<T: Copy + Add<T>> FnOnce<(T,)> for Adder<T> {
//     type Output = <T as Add<T>>::Output;
//     extern "rust-call" fn call_once(self, (a,): (T,)) -> Self::Output {
//         self.0 + a
//     }
// }

// impl<T: Copy + Add<T>> FnMut<(T,)> for Adder<T> {
//     extern "rust-call" fn call_mut(&mut self, (a,): (T,)) -> Self::Output {
//         self.0 + a
//     }
// }

// impl<T: Copy + Add<T>> Fn<(T,)> for Adder<T> {
//     extern "rust-call" fn call(&self, (a,): (T,)) -> Self::Output {
//         self.0 + a
//     }
// }

////////////////////////////////////////////////////////////////////////////////////////

#![recursion_limit = "16384"]

#![feature(fn_traits)]
#![feature(unboxed_closures)]

#[macro_use] extern crate eager;
use eager::{eager, eager_macro_rules};

use std::ops::{Add, FnOnce, FnMut, Fn};

#[derive(Debug, Clone, Copy)]
struct Adder<T: Copy>(T);

eager_macro_rules!{ $eager_1
    macro_rules! adder_func_triangle {
        (LAST($last:ty) $ty:ident $($tys:ident)*) => {
            $ty: Add<$last>,
            adder_func_triangle!(LAST(<$ty as Add<$last>>::Output) $($tys)*)
        };
        (LAST($last:ty)) => { }
    }

    macro_rules! adder_func {
        (($($idents:ident),+):($($tys:ident),+)) => {
            eager! { lazy! { adder_func_inner!{($($idents),+):($($tys),+) BOUNDS(eager! { adder_func_triangle!(LAST(_T) $($tys)+)}) } }}
       };
    }
}

macro_rules! adder_func_last {
    (LAST($last:ty) $ty:ident $($tys:ident)*) => {
        adder_func_last!(LAST(<$ty as Add<$last>>::Output) $($tys)*)
    };
    (LAST($last:ty)) => { $last }
}

macro_rules! adder_func_inner {
    (($($idents:ident),+):($($tys:ident),+) BOUNDS($($bounds:tt)*)) => {
        impl<_T, $($tys),+> FnOnce<($($tys,)+)> for Adder<_T>
        where
            _T: Copy,
            $($bounds)*
        {
            type Output = adder_func_last!(LAST(_T) $($tys)*);
            extern "rust-call" fn call_once(self, ($($idents,)*): ($($tys,)+)) -> Self::Output {
                right_recursive!({self.0} $({$idents})*)
            }
        }

        impl<_T, $($tys),+> FnMut<($($tys,)+)> for Adder<_T>
        where
            _T: Copy,
            $($bounds)*
        {
            extern "rust-call" fn call_mut(&mut self, ($($idents,)*): ($($tys,)+)) -> Self::Output {
                right_recursive!({self.0} $({$idents})*)
            }
        }

        impl<_T, $($tys),+> Fn<($($tys,)+)> for Adder<_T>
        where
            _T: Copy,
            $($bounds)*
        {
            extern "rust-call" fn call(&self, ($($idents,)*): ($($tys,)+)) -> Self::Output {
                right_recursive!({self.0} $({$idents})*)
            }
        }
    };
}

macro_rules! right_recursive {
    ({$a:expr} {$b:expr} $({$rest:expr})*) => {
        right_recursive! { { (($b) + ($a)) } $({$rest})* }
    };

    ({$e:expr}) => { ($e) }
}


adder_func!((a):                                                                                                                                                                                    (A));
adder_func!((a, b):                                                                                                                                                                                 (A, B));
adder_func!((a, b, c):                                                                                                                                                                              (A, B, C));
adder_func!((a, b, c, d):                                                                                                                                                                           (A, B, C, D));
adder_func!((a, b, c, d, e):                                                                                                                                                                        (A, B, C, D, E));
adder_func!((a, b, c, d, e, f):                                                                                                                                                                     (A, B, C, D, E, F));
adder_func!((a, b, c, d, e, f, g):                                                                                                                                                                  (A, B, C, D, E, F, G));
adder_func!((a, b, c, d, e, f, g, h):                                                                                                                                                               (A, B, C, D, E, F, G, H));
adder_func!((a, b, c, d, e, f, g, h, i):                                                                                                                                                            (A, B, C, D, E, F, G, H, I));
adder_func!((a, b, c, d, e, f, g, h, i, j):                                                                                                                                                         (A, B, C, D, E, F, G, H, I, J)) ;
adder_func!((a, b, c, d, e, f, g, h, i, j, k):                                                                                                                                                      (A, B, C, D, E, F, G, H, I, J, K));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l):                                                                                                                                                   (A, B, C, D, E, F, G, H, I, J, K, L));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m):                                                                                                                                                (A, B, C, D, E, F, G, H, I, J, K, L, M));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n):                                                                                                                                             (A, B, C, D, E, F, G, H, I, J, K, L, M, N));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o):                                                                                                                                          (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p):                                                                                                                                       (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q):                                                                                                                                    (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r):                                                                                                                                 (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s):                                                                                                                              (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t):                                                                                                                           (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u):                                                                                                                        (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v):                                                                                                                     (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w):                                                                                                                  (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x):                                                                                                               (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y):                                                                                                            (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z):                                                                                                         (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa):                                                                                                     (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab):                                                                                                 (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac):                                                                                             (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB, AC));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad):                                                                                         (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB, AC, AD));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae):                                                                                     (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB, AC, AD, AE));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af):                                                                                 (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB, AC, AD, AE, AF));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag):                                                                             (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB, AC, AD, AE, AF, AG));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah):                                                                         (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB, AC, AD, AE, AF, AG, AH));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai):                                                                     (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB, AC, AD, AE, AF, AG, AH, AI));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj):                                                                 (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB, AC, AD, AE, AF, AG, AH, AI, AJ));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak):                                                             (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB, AC, AD, AE, AF, AG, AH, AI, AJ, AK));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al):                                                         (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB, AC, AD, AE, AF, AG, AH, AI, AJ, AK, AL));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am):                                                     (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB, AC, AD, AE, AF, AG, AH, AI, AJ, AK, AL, AM));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an):                                                 (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB, AC, AD, AE, AF, AG, AH, AI, AJ, AK, AL, AM, AN));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao):                                             (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB, AC, AD, AE, AF, AG, AH, AI, AJ, AK, AL, AM, AN, AO));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap):                                         (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB, AC, AD, AE, AF, AG, AH, AI, AJ, AK, AL, AM, AN, AO, AP));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq):                                     (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB, AC, AD, AE, AF, AG, AH, AI, AJ, AK, AL, AM, AN, AO, AP, AQ));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar):                                 (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB, AC, AD, AE, AF, AG, AH, AI, AJ, AK, AL, AM, AN, AO, AP, AQ, AR));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, a_s):                             (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB, AC, AD, AE, AF, AG, AH, AI, AJ, AK, AL, AM, AN, AO, AP, AQ, AR, AS));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, a_s, at):                         (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB, AC, AD, AE, AF, AG, AH, AI, AJ, AK, AL, AM, AN, AO, AP, AQ, AR, AS, AT));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, a_s, at, au):                     (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB, AC, AD, AE, AF, AG, AH, AI, AJ, AK, AL, AM, AN, AO, AP, AQ, AR, AS, AT, AU));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, a_s, at, au, av):                 (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB, AC, AD, AE, AF, AG, AH, AI, AJ, AK, AL, AM, AN, AO, AP, AQ, AR, AS, AT, AU, AV));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, a_s, at, au, av, aw):             (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB, AC, AD, AE, AF, AG, AH, AI, AJ, AK, AL, AM, AN, AO, AP, AQ, AR, AS, AT, AU, AV, AW));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, a_s, at, au, av, aw, ax):         (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB, AC, AD, AE, AF, AG, AH, AI, AJ, AK, AL, AM, AN, AO, AP, AQ, AR, AS, AT, AU, AV, AW, AX));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, a_s, at, au, av, aw, ax, ay):     (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB, AC, AD, AE, AF, AG, AH, AI, AJ, AK, AL, AM, AN, AO, AP, AQ, AR, AS, AT, AU, AV, AW, AX, AY));
adder_func!((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, a_s, at, au, av, aw, ax, ay, az): (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z, AA, AB, AC, AD, AE, AF, AG, AH, AI, AJ, AK, AL, AM, AN, AO, AP, AQ, AR, AS, AT, AU, AV, AW, AX, AY, AZ));

macro_rules! units {
    ($($id:ident),*) => {$(
        #[derive(Debug, Copy, Clone, PartialEq, Eq)]
        struct $id;
    )*};
}

units! { Zero, One, Two, Three, Four, Five, Six, Seven, Eight, Nine }

macro_rules! add_impls {
    ($($l:tt + $r:tt => $o:tt),* $(,)?) => {$(
        impl Add<$r> for $l {
            type Output = $o;
            fn add(self, _rhs: $r) -> $o { $o }
        }
    )*};
}

add_impls! {
    Two + Zero => Two,
    Two + Two => Four,
    Four + Two => Six,
    Four + Four => Eight,

    // Zero + Four is _not allowed_.
}

// 2048!
units! { B2, B4, B8, B16, B32, B64, B128, B256, B512, B1024, B2048 }

add_impls!{
    B2 + B2 => B4,
    B4 + B4 => B8,
    B8 + B8 => B16,
    B16 + B16 => B32,
    B32 + B32 => B64,
    B64 + B64 => B128,
    B128 + B128 => B256,
    B256 + B256 => B512,
    B512 + B512 => B1024,
    B1024 + B1024 => B2048,
}

fn main() {
    let a = Adder(Zero);
    assert_eq!(a(Two), Two);

    let add_2048 = Adder(B2);
    assert_eq!(add_2048(B2, B4, B8, B16, B32, B64, B128, B256, B512, B1024), B2048);

    let b = Adder(1);
    assert_eq!(b(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1), 53);
}
