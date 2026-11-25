(** Federer (1969), 4.1.18, p. 375: existence
    of the independently specified original linear q.
    The already proved actual density and boundary
    maps provide an existence witness, sealed afterward. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentBoundary CompactSummableMultivectors
  CompactSummableMultivectorLinear CurrentLonePairImageUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_lone_pair_map_exists]: the linear
    map q in Federer 4.1.18, p. 375, is an
    actual map on the original compact L1 field pairs.
    This existence proof does not assume its later
    surjectivity or any representation of an arbitrary flat current. *)
Theorem current_lone_pair_map_exists (R:realType)
    (h2:(1+1:R)!=0) n m (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x):
  exists Q:Hom (@current_lone_pair_space R h2 n m U hU)
      (@current_space R h2 n U hU m),
    @is_current_lone_pair_map R h2 n m U hU Q.
Proof.
pose P:=@current_lone_pair_space R h2 n m U hU.
pose C:=@current_space R h2 n U hU m.
pose A:=@compact_summable_multivector_current_hom R h2 n m U hU.
pose B:=@compact_summable_multivector_current_hom R h2 n m.+1 U hU.
pose bd:=@current_boundary R h2 n m U hU.
pose F:=fun v:P=>A v.1+bd (B v.2).
have hF:linear F.
  move=>c v w.
  change (A (c*:v.1+w.1)+bd (B (c*:v.2+w.2))=
    c*:(A v.1+bd (B v.2))+(A w.1+bd (B w.2))).
  by rewrite (linearP A) (linearP B) (linearP bd) scalerDr addrACA.
exists (@HomMap R P C F (introT (asboolP _) hF)).
by move=>v.
Qed.
