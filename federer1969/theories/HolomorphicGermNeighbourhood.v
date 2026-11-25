(** Federer (1969), 3.4.12, p. 339: holomorphic
    representatives are holomorphic on an actual open neighbourhood
    of their original centre. The defining local witness and
    the already proved real analytic domain openness supply it. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm
  NormAnalyticLocal HolomorphicAtUP HolomorphicUP HolomorphicGermRepresentatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
(** Source for [holomorphic_germ_open_representative]: select only
    the original holomorphic neighbourhood supplied in the germ
    definition of 3.4.12, p. 339. No representative is
    exposed through a sealed public germ interface. *)
Theorem holomorphic_germ_open_representative (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a
    (f:@holomorphic_representative_type R X NX hNX a):
  exists U:set X,U a /\U `<=` setT /\@open (real_norm_metric_space hNX) U /\
    @is_holomorphic R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX (@complex_modulus_real_norm R)
      U (holomorphic_representative_value f).
Proof.
have [U [hUa hF]]:=holomorphic_representative_holomorphic f.
exists U;split;first exact:hUa.
split;first by move=>x hx.
split;last exact:hF;exact:norm_analytic_domain_open hF.1.
Qed.
