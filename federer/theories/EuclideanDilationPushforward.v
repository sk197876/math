(** Federer (1969), 4.1.2, p. 346: scaling
    a smoothing kernel uses the exact original Lebesgue
    dilation law of 2.7.16. The existing diagonal
    pushforward theorem retains the zero-dimensional atom. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLinearMaps
  EuclideanLebesgueDimensions EuclideanLebesgueLinear MeasureUP MeasurePushforward MeasureScaleIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_inverse_dilation_pushforward]: the
    actual inverse dilation pushes Lebesgue measure to
    epsilon^n times Lebesgue measure, supporting the
    unit-integral formula in Federer 4.1.2, p. 346. *)
Theorem euclidean_inverse_dilation_pushforward (R:realType) n (e:R):0<e ->
  measure_pushforward (fun x:R_n R n=>e^-1*:x) (@euclidean_lebesgue_measure R n)=
    measure_scale (e^+n) (@euclidean_lebesgue_measure R n).
Proof.
move=>he.
have hInv:0<e^-1 by rewrite invr_gt0.
have hEq:(fun x:R_n R n=>e^-1*:x)=(fun x=>@euclidean_diagonal_map R n (fun _=>e^-1) x).
  apply:funext=>x; apply/ffunP=>i; by rewrite /euclidean_diagonal_map /euclidean_diagonal !ffunE.
rewrite hEq; apply:funext=>S.
change (euclidean_lebesgue_measure n ((@euclidean_diagonal_map R n (fun _=>e^-1)) @^-1` S)=
  measure_scale (e^+n) (@euclidean_lebesgue_measure R n) S).
have h:=@euclidean_diagonal_pushforward R n (fun _=>e^-1) (fun _=>hInv) S.
by rewrite prodr_const card_ord exprVn invrK in h.
Qed.
