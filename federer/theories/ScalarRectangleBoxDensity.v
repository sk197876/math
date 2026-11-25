(** Federer (1969), 4.1.23, p. 380:
    the original ordered scalar rectangle R
    is its closed-box top-density current.
    It is normal, has exactly its
    positive finite rectangular volume as mass,
    and has positive finite normal mass,
    including the empty m=0 product. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct FiniteCoordinates FiniteExteriorPowers CurrentSpaces CurrentBoundary
  CurrentMassSealed CurrentMassBasic NormalCurrentsUP NormalCurrentFiniteMass
  CurrentNormalMass SmoothCompactSet TopologicalBorel
  CurrentCharacteristicDensity EuclideanCharacteristicCurrent
  OpenEuclideanCharacteristicCurrent CurrentOpenRestrictionIdentity
  CurrentDomainTransport OrientedRectangleDomain ScalarSegmentFactors
  CurrentScalarRectangle CurrentScalarRectangleVertex ScalarRectangleBox
  ScalarRectangleBoxCoordinates ScalarRectangleBoxMeasurable ScalarRectangleBoxCurrent
  ScalarRectangleIntegralPolyhedral PolyhedralNormal
  ClosedCoordinateBoxConvex ClosedCoordinateBoxGeometry
  CharacteristicCurrentNullBoundary CompactCharacteristicCurrent EuclideanTopCurrentMass
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes
  EuclideanDistributionMeasureContext EuclideanOpenCoordinateBoxUP
  EuclideanOpenCoordinateBoxMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_mass_le_normal_mass]:
    M(R)<=N(R) in the rectangle
    estimate of Federer 4.1.23,
    p. 380, follows directly
    from the original degree-zero exception
    and the positive-degree definition in
    4.1.7, p. 358. *)
Lemma current_mass_le_normal_mass (R : realType) (h2 : (1+1:R)!=0) n
    (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x) m
    (T : @current_space R h2 n U hU m) :
  (@CurrentMass.value R h2 n m U hU T<=@current_normal_mass R h2 n U hU m T)%E.
Proof.
case: m T=> [|m] T; first exact: lexx.
exact: leeDl _ (@current_mass_nonnegative R h2 n m U hU
  (@current_boundary R h2 n m U hU T)).
Qed.

Section RectangleBoxDensity.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variable f : seq (R*R).
Hypothesis hOrdered : @scalar_rectangle_ordered R f.
Local Notation m := (oriented_rectangle_dimension (@scalar_segment_factors R f)).
Local Notation X := (R_n R m).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) x).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation lower := ([ffun i : 'I_m => (nth (0,0) f (val i)).1] : X).
Local Notation upper := ([ffun i : 'I_m => (nth (0,0) f (val i)).2] : X).
Local Notation K := (@closed_coordinate_box_index R m lower upper).
Local Notation C := (@closed_coordinate_box R m lower upper).
Local Notation G := (@scalar_rectangle_box R f).
Local Notation hGM := (@scalar_rectangle_box_measurable R f).
Local Notation hCM := (@euclidean_distribution_measure_borel R m C
  (closed_borel_set (compact_closed (@metric_hausdorff R XT)
    (@closed_coordinate_box_norm_compact R m lower upper)))).
Local Notation top := (e_lambda (@coordinate_basis R m) (ord_tuple m)).
Local Notation Rectangle := (@current_scalar_rectangle R h2 f).
Local Notation Leb := (@euclidean_lebesgue_measure R m).
Local Notation hLeb := (euclidean_lebesgue_is_measure R m).
Local Notation cell := (fun A hA => @current_characteristic_density R h2 m m Leb hLeb
  (@euclidean_distribution_measure_borel R m)
  (@euclidean_distribution_measure_compact_finite R m) A hA top).

(** Source for [scalar_rectangle_endpoints_order]:
    the strict scalar endpoints of
    the actual factor R in Federer
    4.1.23, p. 380, retain
    their original coordinate order. *)
Lemma scalar_rectangle_endpoints_order i : lower i<upper i.
Proof.
have hIndex : (val i<size f)%N by rewrite -(@scalar_rectangle_dimension R f); exact: ltn_ord i.
have h := (allP hOrdered) _ (mem_nth (0,0) hIndex).
by rewrite !ffunE.
Qed.

(** Source for [scalar_rectangle_corners_in_closed_box]:
    every original corner in the
    m! simplex decomposition lies in
    the same containing closed box,
    Federer 4.1.23, p. 380. *)
Lemma scalar_rectangle_corners_in_closed_box x :
  @is_current_scalar_rectangle_vertex R f x -> C x.
Proof.
move=> hx i.
have hVertex : x i=lower i \/ x i=upper i.
  have h := hx i; by rewrite !ffunE.
case: hVertex=> ->; apply/andP; split; try exact: lexx;
  exact: ltW (scalar_rectangle_endpoints_order i).
Qed.

(** Source for [scalar_rectangle_box_density_properties]:
    the chosen factor R in Federer
    4.1.23, p. 380, is
    normal in its exact compact
    coordinate box, has M(R)=Lebesgue(D),
    and 0<N(R)<infinity. Its literal
    closed-box density is retained for the
    subsequent Cartesian factorisation; m=0 is included. *)
Theorem scalar_rectangle_box_density_properties :
  Rectangle=cell C hCM /\
    @normal_currents_supported_in R h2 m Full hFull m K Rectangle /\
    @CurrentMass.value R h2 m m Full hFull Rectangle=Leb C /\
    exists normalMass : R, 0<normalMass /\
      @current_normal_mass R h2 m Full hFull m Rectangle=normalMass%:E.
Proof.
have hProper i : lower i<upper i := scalar_rectangle_endpoints_order i.
have hG : @is_euclidean_open_coordinate_box R m lower upper G.
  split; first exact: hProper.
  move=> x; rewrite scalar_rectangle_box_coordinates.
  split=> hx i; move: (hx i); by rewrite !ffunE.
have hActual : Rectangle=cell G hGM.
  rewrite /current_scalar_rectangle (@scalar_rectangle_box_current R h2 f hOrdered)
    /open_euclidean_characteristic_current /euclidean_characteristic_current.
  exact: current_equal_domain_restriction_identity.
have hClosed : cell G hGM=cell C hCM.
  apply: characteristic_current_nested_null_difference.
  - move=> x hx i; have /andP [hLow hHigh] := (hG.2 x).1 hx i.
    apply/andP; split; exact: ltW.
  - exact: (@proper_coordinate_box_null_boundary R m lower upper G hG).
have hCorners := scalar_rectangle_corners_in_closed_box.
have [_ [_ [_ [_ [_ [_ hIntegral]]]]]] :=
  @scalar_rectangle_integral_polyhedral_decomposition R h2 f K
    (@closed_coordinate_box_convex R m lower upper) hCorners.
have hNormal := @integral_polyhedral_current_normal_support R h2 m m Full hFull
  K Rectangle hIntegral.
have hMass := (@compact_characteristic_current_properties R h2 m m C hCM top
  K (fun _ hx => hx)).1.
rewrite euclidean_top_current_vector_mass_one mul1e in hMass.
have hRectangleMass : @CurrentMass.value R h2 m m Full hFull Rectangle=Leb C.
  by rewrite hActual hClosed.
have hVolume : Leb C=Leb G.
  rewrite (@euclidean_closed_box R m lower upper (fun i => ltW (hProper i)))
    (@open_coordinate_box_volume R m lower upper G hG).
  reflexivity.
have hPositiveMass : (0<@CurrentMass.value R h2 m m Full hFull Rectangle)%E.
  rewrite hRectangleMass hVolume.
  exact: (andP (@open_coordinate_box_positive_finite_volume R m lower upper G hG)).1.
have hNPositive : (0<@current_normal_mass R h2 m Full hFull m Rectangle)%E.
  exact: lt_le_trans hPositiveMass (current_mass_le_normal_mass Rectangle).
have hNFinite := @normal_current_finite_normal_mass R h2 m Full hFull m Rectangle hNormal.1.
have hNumber : @current_normal_mass R h2 m Full hFull m Rectangle \is a fin_num.
  by rewrite (ge0_fin_numE (ltW hNPositive)).
pose normalMass := fine (@current_normal_mass R h2 m Full hFull m Rectangle).
have hN : @current_normal_mass R h2 m Full hFull m Rectangle=normalMass%:E.
  symmetry; exact: fineK hNumber.
have hRealPositive : 0<normalMass by move: hNPositive; rewrite hN lte_fin.
split; first exact: eq_trans hActual hClosed.
split; first exact: hNormal.
split; first exact: hRectangleMass.
exists normalMass; by split.
Qed.
End RectangleBoxDensity.
