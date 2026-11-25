(** Federer (1969), 3.4.8(2), p. 326:
    the original ideal image exists and its independent
    membership law determines it uniquely. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import AnalyticRotatedIdealUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_ideal_image_exists]: the image
    set used for I_g exists, supporting 3.4.8(2), p. 326.
    The direct image serves only as an existence witness. *)
Theorem analytic_ideal_image_exists (A B:comNzRingType) (M:{rmorphism A->B}) (I:set A):
  exists J,is_analytic_ideal_image M I J.
Proof. exists (fun beta=>exists alpha,I alpha /\M alpha=beta)=>beta;reflexivity. Qed.

(** Source for [analytic_ideal_image_unique]: the original
    membership law determines I_g uniquely, supporting
    3.4.8(2), p. 326. *)
Lemma analytic_ideal_image_unique (A B:comNzRingType) (M:{rmorphism A->B})
    (I:set A) (J K:set B):
  is_analytic_ideal_image M I J ->is_analytic_ideal_image M I K ->J=K.
Proof.
move=>hJ hK;apply/seteqP;split=>beta hBeta.
- apply/(hK beta);exact:(hJ beta).1 hBeta.
- apply/(hJ beta);exact:(hK beta).1 hBeta.
Qed.
