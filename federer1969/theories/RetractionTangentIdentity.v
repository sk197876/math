(** Federer (1969), 3.1.22, pp. 235–236: a local
    retraction fixes tangent vectors at points of the retract. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom TensorUP RealNormUP NormMetric NormDifferentialUP
  NormDifferentialLinear NormVanishingTangent TangentConeUP RetractionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_retraction_differential_tangent]: supporting the
    equivalence of (1) and (2) in Federer 3.1.22,
    pp. 235–236. Differentiating the equality r=id on B
    near a, using the opening vanishing observation, gives Dr(v)=v
    for every v in Tan(B,a). No finite dimension is required. *)
Lemma norm_retraction_differential_tangent (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (B T:set X) (r:X->X) a (P:Hom X X) :
  B a -> has_norm_differential NX NX T r a P ->
  (forall x,B x -> T x -> r x=x) ->
  forall v,norm_tangent_cone NX B a v -> P v=v.
Proof.
move=>ha hr hfix v hv.
have hidb:norm_bounded_linear NX NX (hom_of_linear (linear_id X)).
  exists 1; split; first exact: ler01.
  by move=>w; rewrite hom_of_linearE /= mul1r.
have hid:=@norm_differential_linear R X X NX NX hNX hNX T a
  (hom_of_linear (linear_id X)) (norm_differential_interior hr) hidb.
exact (@norm_differentials_agree_on_tangent R X X NX NX hNX hNX T T B r
  (hom_of_linear (linear_id X)) a P (hom_of_linear (linear_id X))
  hr hid (subset_closure ha) (fun x hx ht _=>hfix x hx ht) v hv).
Qed.
