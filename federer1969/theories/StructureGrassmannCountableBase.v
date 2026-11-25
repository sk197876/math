(** Federer (1969), 3.3.10, p. 296: countable-base background
    for the ORIGINAL Grassmann topology, not a replacement carrier. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces EuclideanInnerProduct InnerMetric
  FiniteCoordinates HomInner HomCompositionDeterminant HomSpaceTopology GrassmannHomogeneousSpace
  InnerSpaceCountableBase CountableOpenBaseUP InitialCountableOpenBase.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [structure_grassmann_countable_open_base]: the
    countable-base background needed for the actual product measure
    in Federer 3.3.10, p. 296. The original Grassmann topology is
    induced by its original orthogonal projection into finite
    dimensional Hom. Pull back an existential actual Hom base;
    the auxiliary enumeration stays local. *)
Theorem structure_grassmann_countable_open_base (R:realType) n k:
  exists U:nat->set (grassmann_space
    (@euclidean_inner_productP R k) (@euclidean_inner_productP R n)
    (@coordinate_basisP R k) (@coordinate_basisP R n)),is_countable_open_base U.
Proof.
pose hH:=hom_inner_productP (@euclidean_inner_productP R n)
  (@euclidean_inner_productP R n) (@coordinate_basisP R n).
have [U hU]:=inner_space_countable_open_base hH
  (hom_rank_one_baseP (@coordinate_basisP R n) (@coordinate_basisP R n)).
exists (fun j=>(fun W=>grassmann_projection (@euclidean_inner_productP R k)
  (@euclidean_inner_productP R n) (@coordinate_basisP R k) W) @^-1` U j).
exact:initial_countable_open_base hU.
Qed.
