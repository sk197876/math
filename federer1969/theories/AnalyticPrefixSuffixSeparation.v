(** Federer (1969), 3.4.8(10), pp. 331–332:
    the original prefix and suffix coordinates
    separate source vectors. Apply the basis
    expansion already proved for 1.1.4 and
    the exact original prefix equations. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom LinearBasis FiniteDualDimension Annihilator GrassmannAbbreviations
  FiniteCoordinates AnalyticPrefixCoordinatesUP OrdinalCoordinateTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section PrefixSuffix.
Variable R:realType.
Variable X:lmodType R.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
Variable m:nat.
Hypothesis hMN:(m<=n)%N.
Variable P:Hom X (R_n R m).
Hypothesis hP:is_analytic_prefix_projection omega hMN P.

(** Source for [analytic_original_dual_basis]:
    the original supplied coordinate covectors are
    the dual basis, supporting 3.4.8(10),
    pp. 331–332, by the basis uniqueness
    theorem of 1.1.4, p. 11. *)
Lemma analytic_original_dual_basis i u:omega i u = dual_basis he i u.
Proof.
apply:(@basis_linear_ext R (Choice.clone 'I_n _) X e he R^o
  (hom_as_linear (omega i)) (hom_as_linear (dual_basis he i)))=>j.
by rewrite !hom_as_linearE hDual dual_basisE eq_sym.
Qed.

(** Source for [analytic_original_given_basis_expansion]:
    reconstruct the source vector from the
    original supplied coordinates, supporting
    3.4.8(10), pp. 331–332. Apply
    the existing basis expansion; no new
    coordinate construction is needed. *)
Lemma analytic_original_given_basis_expansion x:x = \sum_i omega i x*:e i.
Proof.
rewrite {1}(basis_vector_expansion he x).
apply:eq_bigr=>i _;by rewrite analytic_original_dual_basis.
Qed.

(** Source for [analytic_prefix_suffix_separate]:
    p_m(v)=0 and all original suffix
    coordinates zero imply v=0, supporting
    the injective joint differential in
    3.4.8(10), pp. 331–332. Empty
    prefixes and suffixes retain their exact meaning. *)
Theorem analytic_prefix_suffix_separate x:
  P x = 0 ->
  (forall j:'I_(n-m),omega (ordinal_coordinate_tail_index hMN j) x = 0) ->x=0.
Proof.
move=>hPrefix hSuffix.
have hZero i:omega i x = 0.
  case:(ltnP (i:nat) m)=>[hSmall|hLarge].
  - pose j:'I_m:=Ordinal hSmall.
    have hIndex:widen_ord hMN j = i by apply:val_inj.
    have h:=congr1 (fun y:R_n R m=>y j) hPrefix.
    by rewrite hP hIndex ffunE in h.
  - have [j hIndex]:=@ordinal_coordinate_tail_complete n m hMN i hLarge.
    by rewrite -hIndex;exact:hSuffix j.
rewrite (analytic_original_given_basis_expansion x).
apply:big1=>i _;by rewrite hZero scale0r.
Qed.
End PrefixSuffix.
