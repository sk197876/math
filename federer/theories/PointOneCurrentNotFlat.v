(** Federer (1969), 4.1.15, p. 373, and the forward
    reference in 4.1.12, p. 369: a compact finite-mass
    current need not be flat. The actual point one-current
    violates the point-support consequence proved earlier in
    this same item. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentMassSealed FlatCurrentsUP CurrentFlatPointSupport
  PointOneCurrent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section PointOneCurrentNotFlat.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X:=(R_n R 1%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation T:=(@point_one_current R h2).

(** Source for [point_one_current_not_flat]: the finite-mass
    counterexample of 4.1.15, p. 373, is not a
    flat current. This discharges exactly the finite-mass
    nonflat example anticipated in 4.1.12, p. 369. *)
Theorem point_one_current_not_flat:
  ~@is_flat_current R h2 1%N 1%N Full hFull T.
Proof.
move=>hFlat;apply:(@point_one_current_nonzero R h2).
exact:(@current_flat_positive_point_support_zero R h2 1%N 0%N
  Full hFull (0:X) Logic.I T hFlat
  (@point_one_current_support_subset R h2)).
Qed.

(** Source for [finite_mass_compact_nonflat_current_exists]: the
    original existence consequence explicitly forwarded by
    Federer 4.1.12, p. 369, and supplied by
    4.1.15, p. 373. All three properties refer
    to the same actual current, without extra hypotheses. *)
Theorem finite_mass_compact_nonflat_current_exists:
  exists S:@current_space R h2 1%N Full hFull 1%N,
    @compact (real_norm_metric_space hNX)
      (@current_support R h2 1%N Full hFull 1%N S) /\
    (@CurrentMass.value R h2 1%N 1%N Full hFull S < +oo)%E /\
    ~@is_flat_current R h2 1%N 1%N Full hFull S.
Proof.
exists T;split;first exact:(@point_one_current_compact R h2).
split;first exact:(@point_one_current_finite_mass R h2).
exact:point_one_current_not_flat.
Qed.
End PointOneCurrentNotFlat.
