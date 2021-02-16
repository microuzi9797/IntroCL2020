Require Import Znumtheory .
Require Import Zdiv .
Require Import ZArith .
Import Z .

Section SimpleChineseRemainder .

Open Scope Z_scope .

Definition modulo (a b n : Z) : Prop := (n | (a - b)) .
Notation "( a == b [ n ])" := (modulo a b n) .

Lemma modulo_tran : forall a b c n : Z, 
    (a == b [ n ]) -> (b == c [ n ]) -> (a == c [ n ]) .
Proof.
  intros a b c n Hab Hbc .
  red in Hab, Hbc |- * .
  cut (a - c = a - b + (b - c)) .
  - intros H .
    rewrite H .
    apply Zdivide_plus_r .
    + trivial .
    + trivial .
  - auto with * .
Qed.

Lemma modulo_plus_subst : forall a b c n : Z,
    (a == b [ n ]) -> (a + c == b + c [ n ]) .
Proof.
  (* to be done *)
  intros a b c n Hab.
  red in Hab |- *.
  cut (a + c - (b + c) = a - b).
  - intros H.
    rewrite H.
    trivial.
  - auto with *.
Qed.

Lemma modulo_mult_subst : forall a b c n : Z,
    (a == b [ n ]) -> (a * c == b * c [ n ]) .
Proof.
  (* to be done *)
  intros a b c n Hab.
  red in Hab |- *.
  cut (a * c - b * c = (a - b) * c).
  - intros H.
    rewrite H.
    apply Zdivide_mult_l.
    trivial.
  - auto with *.
Qed.

Lemma modulo_plus_multiple_of_n : forall a b c m n : Z,
    (a * m + b * n == c[ n ]) <-> (a * m == c [ n ]).
Proof.
  intros a b c m n.
  unfold iff.
  split.
  (* (a * m + b * n == c[ n ]) -> (a * m == c [ n ]) *)
  - intros Hambnc.
    red in Hambnc |- *.
    apply divide_add_cancel_r with (m := b * n).
    + apply Zdivide_factor_l.
    + cut (b * n + (a * m - c) = a * m + b * n - c).
    * intros H.
      rewrite H.
      trivial.
    * auto with *.
  (* (a * m == c [ n ]) -> (a * m + b * n == c[ n ]) *)
  - intros Hamc.
    red in Hamc |- *.
    cut (a * m + b * n - c = a * m - c + b * n).
    + intros H.
      rewrite H.
      apply Zdivide_plus_r.
      * trivial.
      * apply Zdivide_factor_l.
    + auto with *.
Qed.

Hypothesis m n : Z .
Hypothesis co_prime : rel_prime m n .

Theorem modulo_inv : forall m n : Z, rel_prime m n ->
                       exists x : Z, (m * x == 1 [ n ]) .
Proof.
  (* to be done *)
  intros m0 n0 Hrel_prime.
  elim (Zis_gcd_bezout m0 n0 1).
  - intros u v Hbezout_identity.
    exists u.
    rewrite mul_comm.
    apply modulo_plus_multiple_of_n with (b := v).
    rewrite Hbezout_identity.
    red.
    rewrite sub_diag.
    apply Zdivide_0.
  - trivial.
Qed.

Theorem SimpleChineseRemainder : forall a b : Z,
  exists x : Z, (x == a [ m ]) /\ (x == b [ n ]) .
Proof.
  (* to be done *)
  intros a b.
  destruct (rel_prime_bezout _ _ co_prime) as [u v Hbezout_identity].
  exists (a * v * n + b * u * m).
  split.
  (* (a * v * n + b * u * m == a [ m ]) *)
  - apply add_move_l in Hbezout_identity.
    rewrite <- mul_assoc.
    rewrite Hbezout_identity.
    cut (a * (1 - u * m) + b * u * m = a * 1 + (b * u - a * u) * m).
    + intros H.
      rewrite H.
      apply modulo_plus_multiple_of_n.
      rewrite mul_1_r.
      red.
      rewrite sub_diag.
      apply Zdivide_0.
    + auto with *.
  (* (a * v * n + b * u * m == b [ n ]) *)
  - apply add_move_r in Hbezout_identity.
    rewrite add_comm.
    rewrite <- mul_assoc.
    rewrite Hbezout_identity.
    cut (b * (1 - v * n) + a * v * n = b * 1 + (a * v - b * v) * n).
    + intros H.
      rewrite H.
      apply modulo_plus_multiple_of_n.
      rewrite mul_1_r.
      red.
      rewrite sub_diag.
      apply Zdivide_0.
    + auto with *.
Qed.

End SimpleChineseRemainder .

Check SimpleChineseRemainder .