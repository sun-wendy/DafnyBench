// include "ct_std2rev_model.dfy"

// abstract module ntt_impl {
//     import opened Seq
//     import opened Power
//     import opened Power2
//     import opened DivMod
//     import opened Mul

//         import opened pows_of_2
//     import opened ntt_index
//     import opened ntt_512_params
//         import opened mq_polys
//         import opened poly_view
//     import opened nth_root
//     import opened forward_ntt

//     method j_loop(a: elems, p: elems, t: pow2_t, d: pow2_t, j: nat, u: nat, ghost view: loop_view)
//     returns (a': elems)
//         requires u == j * (2 * d.full);
//         requires view.j_loop_inv(a, d, j);
//         requires t == view.lsize();
//         requires p == rev_mixed_powers_mont_table();
//         requires j < view.lsize().full;
//         ensures view.j_loop_inv(a', d, j + 1);
//     {
//         view.s_loop_inv_pre_lemma(a, d, j);

//         assert  (2 * j) * d.full == j * (2 * d.full) by {
//             LemmaMulProperties();
//         }

//         rev_mixed_powers_mont_table_lemma(t, d, j);
//         var w := p[t.full + j];
//         // modmul(x_value(2 * j, d), R);

//         var s := u;
//         a' := a;

//         ghost var bi := 0;

//         while (s < u + d.full)
//             invariant view.s_loop_inv(a', d, j, s-u);
//         {
//             var a :elems := a';
//             var bi := s-u;

//             var _ := view.higher_points_view_index_lemma(a, d, j, bi);

//             var e := a[s];
//             var o := a[s + d.full];

//             var x := montmul(o, w);
//             a' := a[s+d.full := mqsub(e, x)];
//             a' := a'[s := mqadd(e, x)];
//             s := s + 1;

//             view.s_loop_inv_peri_lemma(a, a', d, j, bi);
//         }

//         assert s == u + d.full;
//         view.s_loop_inv_post_lemma(a', d, j, d.full);
//     }

//     method t_loop(a: elems, p: elems, t: pow2_t, d: pow2_t, ghost coeffs: elems)
//         returns (a': elems)
//         requires 0 <= d.exp < N.exp;
//         requires t_loop_inv(a, pow2_double(d), coeffs);
//         requires p == rev_mixed_powers_mont_table();
//         requires t == block_size(pow2_double(d));
//         ensures t_loop_inv(a', d, coeffs);
//     {
//         ghost var view := build_loop_view(coeffs, d);
//         view.j_loop_inv_pre_lemma(a, d);

//         var j := 0;
//         var u: nat := 0;
//         a' := a;

//         while (j < t.full)
//             invariant t == view.lsize();
//             invariant u == j * (2 * d.full);
//             invariant view.j_loop_inv(a', d, j);
//         {
//             a' := j_loop(a', p, t, d, j, u, view);

//             calc == {
//                 u + 2 * d.full;
//                 j * (2 * d.full) + 2 * d.full;
//                 {
//                     LemmaMulProperties();
//                 }
//                 (j + 1) * (2 * d.full);
//             }

//             j := j + 1;
//             u := u + 2 * d.full;
//         }

//         view.j_loop_inv_post_lemma(a', d, j);
//     }

//     method mulntt_ct(a: elems, p: elems)
//         returns (a': elems)
//         requires N == pow2_t_cons(512, 9);
//         requires p == rev_mixed_powers_mont_table();
//         ensures points_eval_inv(a', a, x_value, pow2(0));
//     {
//         var d := pow2(9);

//         assert d == N by {
//             Nth_root_lemma();
//         }

//         var t := pow2(0);

//         ghost var coeffs := a;
//         t_loop_inv_pre_lemma(a);

//         a' := a;

//         while (t.exp < 9)
//             invariant 0 <= d.exp <= N.exp;
//             invariant t == block_size(d);
//             invariant t_loop_inv(a', d, coeffs);
//         {
//             d := pow2_half(d);
//             a' := t_loop(a', p, t, d, coeffs);
//             t := pow2_double(t);
//         }
    
//         t_loop_inv_post_lemma(a', d, coeffs);
//     }
// }
