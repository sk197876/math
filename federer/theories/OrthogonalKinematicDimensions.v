(** Federer (1969), 3.2.48, pp. 284–286: natural
    source, target and fibre dimensions. For ambient dimension
    d+1, mu=d(d-1)/2 and nu=mu+d; this avoids
    truncated negative intermediate dimensions when d=0. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import EuclideanStiefelVolumeDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope nat_scope.

(** Source for [orthogonal_kinematic_dimension_sum]: source
    dimension equals target plus fibre dimension, as in
    the coarea substitution of 3.2.48, p. 284.
    All natural degrees satisfying d<=k+m are retained. *)
Lemma orthogonal_kinematic_dimension_sum d k m:
  d<=k+m ->
  (k+d*(d-1)%/2)+(m+d*(d-1)%/2)=
    d.+1*(d.+1-1)%/2+((k+m-d)+d*(d-1)%/2).
Proof.
move=>hkm; pose mu:=d*(d-1)%/2.
have hKM:k+m=d+(k+m-d) by rewrite [d+(k+m-d)]addnC subnK.
have hNu:=euclidean_skew_dimension_successor d.
change (d.+1*(d.+1-1)%/2=mu+d) in hNu.
change ((k+mu)+(m+mu)=d.+1*(d.+1-1)%/2+((k+m-d)+mu)).
rewrite [LHS]addnACA {1}hKM hNu [mu+d]addnC -!addnA.
by rewrite (addnCA (k+m-d) mu mu).
Qed.

(** Source for [orthogonal_kinematic_target_dimension_bound]:
    the admissible coarea dimension inequality in 3.2.48,
    p. 284, including the zero-dimensional group O(1). *)
Lemma orthogonal_kinematic_target_dimension_bound d k m:
  d<=k+m ->d.+1*(d.+1-1)%/2<=(k+d*(d-1)%/2)+(m+d*(d-1)%/2).
Proof.
move=>hkm; rewrite (orthogonal_kinematic_dimension_sum hkm); exact:leq_addr.
Qed.

(** Source for [orthogonal_kinematic_fibre_dimension]: the actual
    fibre degree in 3.2.48, p. 284, is lambda+mu.
    No subtraction below zero or positive-degree assumption occurs. *)
Lemma orthogonal_kinematic_fibre_dimension d k m:
  d<=k+m ->
  ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))-d.+1*(d.+1-1)%/2=
    (k+m-d)+d*(d-1)%/2.
Proof. by move=>hkm; rewrite (orthogonal_kinematic_dimension_sum hkm) addKn. Qed.
