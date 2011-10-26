(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

Copyright (C) 2010 Sylvie Boldo
#<br />#
Copyright (C) 2010 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

(** * Functions for computing the number of digits of integers
      and related theorems. *)

Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_float_prop.
Require Import Fcore_digits.

Section Fcalc_digits.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Notation digits := (Zdigits beta).

Theorem digits_abs :
  forall n, digits (Zabs n) = digits n.
Proof.
now intros [|n|n].
Qed.

Theorem digits_ln_beta :
  forall n,
  n <> Z0 ->
  digits n = ln_beta beta (Z2R n).
Proof.
intros n Hn.
destruct (ln_beta beta (Z2R n)) as (e, He) ; simpl.
specialize (He (Z2R_neq _ _ Hn)).
rewrite <- Z2R_abs in He.
assert (Hd := Zdigits_correct beta n).
assert (Hd' := Zdigits_gt_0 beta n).
apply Zle_antisym ; apply (bpow_lt_bpow beta).
apply Rle_lt_trans with (2 := proj2 He).
rewrite <- Z2R_Zpower by omega.
now apply Z2R_le.
apply Rle_lt_trans with (1 := proj1 He).
rewrite <- Z2R_Zpower by omega.
now apply Z2R_lt.
Qed.

Theorem digits_ge_0 :
  forall n, (0 <= digits n)%Z.
Proof.
intros n.
destruct (Z_eq_dec n 0) as [H|H].
now rewrite H.
apply Zlt_le_weak.
now apply Zdigits_gt_0.
Qed.

Theorem ln_beta_F2R_digits :
  forall m e, m <> Z0 ->
  (ln_beta beta (F2R (Float beta m e)) = digits m + e :> Z)%Z.
Proof.
intros m e Hm.
rewrite ln_beta_F2R with (1 := Hm).
apply (f_equal (fun v => Zplus v e)).
apply sym_eq.
now apply digits_ln_beta.
Qed.

Theorem digits_shift :
  forall m e,
  m <> Z0 -> (0 <= e)%Z ->
  digits (m * Zpower beta e) = (digits m + e)%Z.
Proof.
intros m e Hm He.
rewrite <- ln_beta_F2R_digits with (1 := Hm).
rewrite digits_ln_beta.
rewrite Z2R_mult.
now rewrite Z2R_Zpower with (1 := He).
contradict Hm.
apply Zmult_integral_l with (2 := Hm).
apply neq_Z2R.
rewrite Z2R_Zpower with (1 := He).
apply Rgt_not_eq.
apply bpow_gt_0.
Qed.

Theorem digits_Zpower :
  forall e,
  (0 <= e)%Z ->
  digits (Zpower beta e) = (e + 1)%Z.
Proof.
intros e He.
rewrite <- (Zmult_1_l (Zpower beta e)).
rewrite digits_shift ; try easy.
apply Zplus_comm.
Qed.

Theorem digits_le :
  forall x y,
  (0 <= x)%Z -> (x <= y)%Z ->
  (digits x <= digits y)%Z.
Proof.
intros x y Hx Hxy.
case (Z_lt_le_dec 0 x).
clear Hx. intros Hx.
rewrite 2!digits_ln_beta.
apply ln_beta_monotone.
now apply (Z2R_lt 0).
now apply Z2R_le.
apply Zgt_not_eq.
now apply Zlt_le_trans with x.
now apply Zgt_not_eq.
intros Hx'.
rewrite (Zle_antisym _ _ Hx' Hx).
apply digits_ge_0.
Qed.

Theorem lt_digits :
  forall x y,
  (0 <= y)%Z ->
  (digits x < digits y)%Z ->
  (x < y)%Z.
Proof.
intros x y Hy.
cut (y <= x -> digits y <= digits x)%Z. omega.
now apply digits_le.
Qed.

Theorem Zpower_le_digits :
  forall e x,
  (e < digits x)%Z ->
  (Zpower beta e <= Zabs x)%Z.
Proof.
intros [|e|e] x Hex.
(* *)
apply (Zlt_le_succ 0).
apply lt_digits.
apply Zabs_pos.
now rewrite digits_abs.
2: apply Zabs_pos.
(* *)
apply le_Z2R.
rewrite Z2R_Zpower. 2: easy.
assert (Zx: x <> Z0).
intros H.
apply Zlt_not_le with (1 := Hex).
now rewrite H.
revert Hex.
rewrite digits_ln_beta with (1 := Zx).
destruct (ln_beta beta (Z2R x)) as (ex, Ex).
unfold ln_beta_val.
specialize (Ex (Z2R_neq _ 0 Zx)).
intros Hex.
rewrite <- Z2R_abs in Ex.
apply Rle_trans with (2 := proj1 Ex).
apply bpow_le.
omega.
Qed.

Theorem digits_le_Zpower :
  forall e x,
  (Zabs x < Zpower beta e)%Z ->
  (digits x <= e)%Z.
Proof.
intros e x.
generalize (Zpower_le_digits e x).
omega.
Qed.

Theorem digits_gt_Zpower :
  forall e x,
  (Zpower beta e <= Zabs x)%Z ->
  (e < digits x)%Z.
Proof.
intros [|e|e] x Hex.
(* *)
apply Zlt_le_trans with 1%Z.
apply refl_equal.
rewrite <- digits_abs.
change 1%Z with (digits 1).
now apply digits_le.
(* *)
rewrite (Zpred_succ (Zpos e)).
apply Zlt_le_trans with (1 := Zlt_pred _).
unfold Zsucc.
rewrite <- digits_Zpower. 2: easy.
rewrite <- (digits_abs x).
apply digits_le with (2 := Hex).
apply le_Z2R.
rewrite Z2R_Zpower.
apply bpow_ge_0.
easy.
(* *)
apply Zlt_le_trans with Z0.
apply refl_equal.
apply digits_ge_0.
Qed.

Theorem Zpower_gt_digits :
  forall e x,
  (digits x <= e)%Z ->
  (Zabs x < Zpower beta e)%Z.
Proof.
intros e x Hex.
generalize (digits_gt_Zpower e x).
omega.
Qed.

(** Characterizes the number digits of a product.

This strong version is needed for proofs of division and square root
algorithms, since they involve operation remainders.
*)

Theorem digits_mult_strong :
  forall x y,
  (0 <= x)%Z -> (0 <= y)%Z ->
  (digits (x + y + x * y) <= digits x + digits y)%Z.
Proof.
intros x y Hx Hy.
case (Z_lt_le_dec 0 x).
clear Hx. intros Hx.
case (Z_lt_le_dec 0 y).
clear Hy. intros Hy.
(* . *)
assert (Hxy: (0 < Z2R (x + y + x * y))%R).
apply (Z2R_lt 0).
change Z0 with (0 + 0 + 0)%Z.
apply Zplus_lt_compat.
now apply Zplus_lt_compat.
now apply Zmult_lt_0_compat.
rewrite 3!digits_ln_beta ; try now (apply sym_not_eq ; apply Zlt_not_eq).
apply ln_beta_le with (1 := Rgt_not_eq _ _ Hxy).
rewrite Rabs_pos_eq with (1 := Rlt_le _ _ Hxy).
destruct (ln_beta beta (Z2R x)) as (ex, Hex). simpl.
specialize (Hex (Rgt_not_eq _ _ (Z2R_lt _ _ Hx))).
destruct (ln_beta beta (Z2R y)) as (ey, Hey). simpl.
specialize (Hey (Rgt_not_eq _ _ (Z2R_lt _ _ Hy))).
apply Rlt_le_trans with (Z2R (x + 1) * Z2R (y + 1))%R.
rewrite <- Z2R_mult.
apply Z2R_lt.
apply Zplus_lt_reg_r with (- (x + y + x * y + 1))%Z.
now ring_simplify.
rewrite bpow_plus.
apply Rmult_le_compat ; try (apply (Z2R_le 0) ; omega).
rewrite <- (Rmult_1_r (Z2R (x + 1))).
change (F2R (Float beta (x + 1) 0) <= bpow ex)%R.
apply F2R_p1_le_bpow.
exact Hx.
unfold F2R. rewrite Rmult_1_r.
apply Rle_lt_trans with (Rabs (Z2R x)).
apply RRle_abs.
apply Hex.
rewrite <- (Rmult_1_r (Z2R (y + 1))).
change (F2R (Float beta (y + 1) 0) <= bpow ey)%R.
apply F2R_p1_le_bpow.
exact Hy.
unfold F2R. rewrite Rmult_1_r.
apply Rle_lt_trans with (Rabs (Z2R y)).
apply RRle_abs.
apply Hey.
apply neq_Z2R.
now apply Rgt_not_eq.
(* . *)
intros Hy'.
rewrite (Zle_antisym _ _ Hy' Hy).
rewrite Zmult_0_r, 3!Zplus_0_r.
apply Zle_refl.
intros Hx'.
rewrite (Zle_antisym _ _ Hx' Hx).
rewrite Zmult_0_l, Zplus_0_r, 2!Zplus_0_l.
apply Zle_refl.
Qed.

Theorem digits_mult :
  forall x y,
  (digits (x * y) <= digits x + digits y)%Z.
Proof.
intros x y.
rewrite <- digits_abs.
rewrite <- (digits_abs x).
rewrite <- (digits_abs y).
apply Zle_trans with (digits (Zabs x + Zabs y + Zabs x * Zabs y)).
apply digits_le.
apply Zabs_pos.
rewrite Zabs_Zmult.
generalize (Zabs_pos x) (Zabs_pos y).
omega.
apply digits_mult_strong ; apply Zabs_pos.
Qed.

Theorem digits_mult_ge :
  forall x y,
  (x <> 0)%Z -> (y <> 0)%Z ->
  (digits x + digits y - 1 <= digits (x * y))%Z.
Proof.
intros x y Zx Zy.
cut ((digits x - 1) + (digits y - 1) < digits (x * y))%Z. omega.
apply digits_gt_Zpower.
rewrite Zabs_Zmult.
rewrite Zpower_exp.
apply Zmult_le_compat.
apply Zpower_le_digits.
apply Zlt_pred.
apply Zpower_le_digits.
apply Zlt_pred.
apply Zpower_ge_0.
apply Zpower_ge_0.
generalize (Zdigits_gt_0 beta x). omega.
generalize (Zdigits_gt_0 beta y). omega.
Qed.

Theorem digits_shr :
  forall m e,
  (0 <= m)%Z ->
  (0 <= e <= digits m)%Z ->
  digits (m / Zpower beta e) = (digits m - e)%Z.
Proof.
intros m e Hm He.
destruct (Zle_lt_or_eq 0 m Hm) as [Hm'|Hm'].
(* *)
destruct (Zle_lt_or_eq _ _ (proj2 He)) as [He'|He'].
(* . *)
unfold Zminus.
rewrite <- ln_beta_F2R_digits.
2: now apply Zgt_not_eq.
assert (Hp: (0 < Zpower beta e)%Z).
apply lt_Z2R.
rewrite Z2R_Zpower with (1 := proj1 He).
apply bpow_gt_0.
rewrite digits_ln_beta.
rewrite <- Zfloor_div with (1 := Zgt_not_eq _ _ Hp).
rewrite Z2R_Zpower with (1 := proj1 He).
unfold Rdiv.
rewrite <- bpow_opp.
change (Z2R m * bpow (-e))%R with (F2R (Float beta m (-e))).
destruct (ln_beta beta (F2R (Float beta m (-e)))) as (e', E').
simpl.
specialize (E' (Rgt_not_eq _ _ (F2R_gt_0_compat beta (Float beta m (-e)) Hm'))).
apply ln_beta_unique.
rewrite Rabs_pos_eq in E'.
2: now apply F2R_ge_0_compat.
rewrite Rabs_pos_eq.
split.
assert (H': (0 <= e' - 1)%Z).
(* .. *)
cut (1 <= e')%Z. omega.
apply bpow_lt_bpow with beta.
apply Rle_lt_trans with (2 := proj2 E').
simpl.
rewrite <- (Rinv_r (bpow e)).
rewrite <- bpow_opp.
unfold F2R. simpl.
apply Rmult_le_compat_r.
apply bpow_ge_0.
rewrite <- Z2R_Zpower with (1 := proj1 He).
apply Z2R_le.
rewrite <- Zabs_eq with (1 := Hm).
now apply Zpower_le_digits.
apply Rgt_not_eq.
apply bpow_gt_0.
(* .. *)
rewrite <- Z2R_Zpower with (1 := H').
apply Z2R_le.
apply Zfloor_lub.
rewrite Z2R_Zpower with (1 := H').
apply E'.
apply Rle_lt_trans with (2 := proj2 E').
apply Zfloor_lb.
apply (Z2R_le 0).
apply Zfloor_lub.
now apply F2R_ge_0_compat.
apply Zgt_not_eq.
apply Zlt_le_trans with (beta^e / beta^e)%Z.
rewrite Z_div_same_full.
apply refl_equal.
now apply Zgt_not_eq.
apply Z_div_le.
now apply Zlt_gt.
rewrite <- Zabs_eq with (1 := Hm).
now apply Zpower_le_digits.
(* . *)
unfold Zminus.
rewrite He', Zplus_opp_r.
rewrite Zdiv_small.
apply refl_equal.
apply conj with (1 := Hm).
pattern m at 1 ; rewrite <- Zabs_eq with (1 := Hm).
apply Zpower_gt_digits.
apply Zle_refl.
(* *)
revert He.
rewrite <- Hm'.
intros (H1, H2).
simpl.
now rewrite (Zle_antisym _ _ H2 H1).
Qed.

End Fcalc_digits.

Definition radix2 := Build_radix 2 (refl_equal _).

Theorem Z_of_nat_S_digits2_Pnat :
  forall m : positive,
  Z_of_nat (S (digits2_Pnat m)) = Zdigits radix2 (Zpos m).
Proof.
intros m.
rewrite digits_ln_beta. 2: easy.
apply sym_eq.
apply ln_beta_unique.
generalize (digits2_Pnat m) (digits2_Pnat_correct m).
intros d H.
simpl in H.
replace (Z_of_nat (S d) - 1)%Z with (Z_of_nat d).
rewrite <- Z2R_abs.
rewrite <- 2!Z2R_Zpower_nat.
split.
now apply Z2R_le.
now apply Z2R_lt.
rewrite inj_S.
apply Zpred_succ.
Qed.

Notation digits := Zdigits (only parsing).
