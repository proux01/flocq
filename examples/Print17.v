(**
This example is part of the Flocq formalization of floating-point
arithmetic in Coq: https://flocq.gitlabpages.inria.fr/

Copyright (C) 2021 Pierre Roux

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

(** * Decimal printing of binary64 with 17 digits is enough. *)

From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Core.

Open Scope R_scope.

Section Print_generic.

(** radix of the initial format *)
Variable ri : radix.

(** emin and precision of the initial format *)
Variable emini pi : Z.
Context { prec_gt_0_ : Prec_gt_0 pi }.

(** radix and precision of printing format *)
Variable (rp : radix) (pp : Z).

(** main hypothesis:
if [pp] is large enough, printing then parsing will be the identity *)
Hypothesis pp_large_enough : bpow ri pi < bpow rp (pp - 1).

Variable tie : Z -> bool.

(** if [printed_x] is a rounding to nearest of float value [x] with at least
[pp] figures in radix [rp], then parsing [printed_x]
with a rounding to nearest at precision [pi] in radix [ri] yields back [x]. *)
Lemma print_generic :
  forall x, 0 < x -> generic_format ri (FLT_exp emini pi) x ->
  forall printed_x, Rabs (x - printed_x) <= /2 * bpow rp (mag rp x - pp) ->
  round ri (FLT_exp emini pi) (Znearest tie) printed_x = x.
Proof.
intros x xgt0 Fx y y_err.
assert (le_bpow_p : bpow rp (- (pp - 1)) < bpow ri (- pi)).
{ now rewrite !bpow_opp; apply Rinv_lt; [apply bpow_gt_0|]. }
assert (Vexp : Valid_exp (FLT_exp emini pi)) by now apply FLT_exp_valid.
assert (Vrnd : Valid_rnd (Znearest tie)) by now apply valid_rnd_N.
assert (bpow_x : bpow rp (mag rp x - pp) <= x * bpow rp (- (pp - 1))).
{ replace (_ - pp)%Z with (mag rp x - 1 + - (pp - 1))%Z by ring.
  rewrite bpow_plus; apply Rmult_le_compat_r; [apply bpow_ge_0|].
  apply (Rle_trans _ (Rabs x)); [|rewrite Rabs_pos_eq; lra].
  apply bpow_mag_le; lra. }
assert (bpow_lt_ulp : bpow rp (mag rp x - pp) < ulp ri (FLT_exp emini pi) x).
{ unfold ulp, cexp; (rewrite Req_bool_false; [|lra]).
  apply (Rlt_le_trans _ (bpow ri (mag ri x - pi))).
  2:{ now apply bpow_le, Z.le_max_l. }
  apply (Rle_lt_trans _ _ _ bpow_x).
  apply (Rlt_trans _ (x * bpow ri (- pi))).
  2:{ unfold Z.sub; rewrite bpow_plus.
    apply Rmult_lt_compat_r; [now apply bpow_gt_0|].
    apply (Rle_lt_trans _ (Rabs x)); [rewrite Rabs_pos_eq; lra|].
    apply bpow_mag_gt. }
  apply Rmult_lt_compat_l; lra. }
assert (bpow_lt_ulpp : bpow rp (mag rp x - pp)
                       < ulp ri (FLT_exp emini pi)
                             (pred ri (FLT_exp emini pi) x)).
{ case (ulp_FLT_pred_pos _ _ _ x Fx (Rlt_le _ _ xgt0)) as [rx|[xpow rx]];
    rewrite rx; [exact bpow_lt_ulp|].
  unfold ulp, cexp; (rewrite Req_bool_false; [|lra]).
  apply (Rlt_le_trans _ (bpow ri (mag ri x - pi + -1))).
  2:{ unfold Rdiv; rewrite <-bpow_1, <-bpow_opp.
    unfold FLT_exp; rewrite <-bpow_plus, <-Z.add_max_distr_r.
    apply bpow_le, Z.le_max_l. }
  apply (Rle_lt_trans _ _ _ bpow_x).
  replace (_ + -1)%Z with (mag ri x - 1 + -pi)%Z by ring.
  rewrite bpow_plus, <-xpow.
  apply Rmult_lt_compat_l; lra. }
case (Rle_or_lt x y); [intros [xlty|<-]; [|now apply round_generic]|intro yltx].
{ apply Rle_antisym; [|now apply round_ge_generic; [..|apply Rlt_le]].
  apply round_N_le_midp; [assumption..|].
  rewrite succ_eq_pos; [|now apply Rlt_le].
  replace (_ / 2) with (x + /2 * ulp ri (FLT_exp emini pi) x) by field.
  assert (y_err' : y - x <= /2 * bpow rp (mag rp x - pp)).
  { revert y_err; apply Rle_trans; rewrite Rabs_minus_sym, Rabs_pos_eq; lra. }
  lra. }
apply Rle_antisym; [now apply round_le_generic; [..|apply Rlt_le]|].
apply round_N_ge_midp; [assumption..|].
assert (y_err' : (x + (x - bpow rp (mag rp x - pp))) / 2 <= y).
{ apply (Rplus_le_reg_r (- x)).
  field_simplify; replace (-x + y) with (- (x - y)) by ring.
  unfold Rdiv; rewrite <-Ropp_mult_distr_l; apply Ropp_le_contravar.
  rewrite <-(Rabs_pos_eq (x - y)); lra. }
revert y_err'; apply Rlt_le_trans.
apply Rmult_lt_compat_r; [lra|apply Rplus_lt_compat_l].
apply (Rplus_lt_reg_r (ulp ri (FLT_exp emini pi)
                           (pred ri (FLT_exp emini pi) x))).
now rewrite pred_plus_ulp; [lra|..].
Qed.

End Print_generic.

Section Print17.

Variable emin : Z.
Let prec := 53%Z.

Let radix10 := Build_radix 10 eq_refl.

Variable tie : Z -> bool.

(** if [printed_x] is a rounding to nearest of binary64 value [x] with at least
17 digits, then parsing [printed_x] with a radix2 rounding to nearest
yields back [x]. *)
Lemma print17 :
  forall x, 0 < x -> generic_format radix2 (FLT_exp emin prec) x ->
  forall printed_x,
  Rabs (x - printed_x) <= /2 * bpow radix10 (mag radix10 x - 17) ->
  round radix2 (FLT_exp emin prec) (Znearest tie) printed_x = x.
Proof. now apply print_generic; compute; [|lra]. Qed.

End Print17.
