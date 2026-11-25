(** Federer (1969), 2.5.20, p. 114: the support of k(x) lies in the fibre of
    spt mu almost everywhere. Countable basic rectangles and countably many
    uniformly dense supported tests give one common exceptional null set.
    The scalar uniqueness argument and compact cutoff ingredients are cited
    in DaniellRectangleNullPairing.v and CompactFunctionSupportedTests.v.
    editions: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import HausdorffBinaryProduct MeasureUP MeasureAlmostUP MeasureAlmostBasic RadonMeasureUP
  RealIntegralFunctionalUP FunctionLatticeRegularityUP CompactSupportFunctionUP
  CompactSupportDaniellSupport DaniellIntegralUP DaniellSpaceWeakTopology
  DaniellDisintegrationUP DaniellRectangleNullPairing CompactFunctionSupportedTests
  DaniellSupportedTests CountableOpenBaseUP CountableProductRectangle CompactMetricSeparability
  SubtypeCompactHausdorff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_daniell_decomposition_support]: the
    support assertion following the first displayed integral
    in Federer 2.5.20, p. 114. Regularity and the
    representing functional here are properties of the variation
    measure produced by 2.5.12; the final existence theorem
    supplies them rather than assuming a disintegration. *)
Theorem compact_daniell_decomposition_support (R : realType) (X Y : metricType R)
    (phi : set X -> \bar R) (mu : ((X*Y) -> R) -> R) (F : (X -> R) -> R)
    (k : X -> daniell_weak_space (@compactly_supported_continuous_functions R Y)) :
  compact (@setT X) -> compact (@setT Y) -> is_measure phi -> is_radon_measure phi ->
  is_real_integral_functional phi (@compactly_supported_continuous_functions R X) F ->
  is_function_lattice_regular (@compactly_supported_continuous_functions R X) phi ->
  is_daniell_integral (@compactly_supported_continuous_functions R (X*Y)%type) mu ->
  is_daniell_integral_decomposition phi mu k -> daniell_decomposition_support_property phi mu k.
Proof.
move=> hX hY hm hr hrep hreg hmu hk.
have [B hB] := compact_metric_countable_open_base hX.
have [C hC] := compact_metric_countable_open_base hY.
have hexX n := @countable_supported_test_family_exists R X B (B n) hX hB.
have hexY n := @countable_supported_test_family_exists R Y C (C n) hY hC.
pose DX n := projT1 (cid (hexX n)).
pose DY n := projT1 (cid (hexY n)).
have hDX n := projT2 (cid (hexX n)).
have hDY n := projT2 (cid (hexY n)).
pose H i j := B i `*` C j `<=` ~` compact_support_daniell_support mu.
have hp i j : measure_almost_everywhere phi [set x |
    H i j -> forall g, DX i g -> forall f, DY j f -> g x*k x f=0].
  case: (pselect (H i j))=> hij.
  - have hg g : DX i g -> measure_almost_everywhere phi
        [set x | forall f, DY j f -> g x*k x f=0].
      move=> hgi; have [hgK hgS] := supported_tests_member (hDX i) hgi.
      apply: (@measure_almost_everywhere_countable R X [the choiceType of Y -> R]
        phi hm (DY j) (fun f => [set x | g x*k x f=0])
        (supported_tests_countable (hDY j)))=> f hfj.
      have [hfK hfS] := supported_tests_member (hDY j) hfj.
      exact: (@daniell_rectangle_supported_pairing_zero R X Y phi mu F k (B i) (C j) g f
        (hausdorff_binary_product (@metric_hausdorff R X) (@metric_hausdorff R Y)) hX hY hm hr hrep hreg
        hmu hk hij hgK hgS hfK hfS).
    have hall := @measure_almost_everywhere_countable R X [the choiceType of X -> R]
      phi hm (DX i) (fun g => [set x | forall f, DY j f -> g x*k x f=0])
      (supported_tests_countable (hDX i)) hg.
    apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ hall)=> x hx _.
    exact hx.
  - apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ (measure_almost_everywhere_true hm)).
    move=> x _ h; exact: False_ind _ (hij h).
have hrow i := @measure_almost_everywhere_countable R X [the choiceType of (nat : Type)]
  phi hm setT (fun j => [set x | H i j -> forall g, DX i g -> forall f, DY j f -> g x*k x f=0])
  (countableP setT) (fun j _ => hp i j).
have hall := @measure_almost_everywhere_countable R X [the choiceType of (nat : Type)]
  phi hm setT (fun i => \bigcap_(j in setT)
    [set x | H i j -> forall g, DX i g -> forall f, DY j f -> g x*k x f=0])
  (countableP setT) (fun i _ => hrow i).
apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ hall)=> x hx y hy.
apply: contrapT=> hxy.
have hopen : open (~` compact_support_daniell_support mu).
  by rewrite openC; exact: compact_support_daniell_support_closed.
have [i [j [hix [hjy hij]]]] := countable_product_rectangle_refines hB hC hopen hxy.
have [g [hg hgx]] := supported_tests_cover_open_set (radon_hausdorff hr)
  (radon_locally_compact hr) (countable_base_open hB i) (hDX i) hix.
have hz f : DY j f -> k x f=0.
  move=> hf; have hpair := hx i I j I hij g hg f hf.
  move/eqP: hpair; rewrite mulf_eq0; move/orP=> [/eqP hz|/eqP hz]; last exact hz.
  exact: False_ind _ (hgx hz).
exact: (daniell_supported_tests_exclude_open_set hY (countable_base_open hC j)
  (daniell_decomposition_values hk x) (hDY j) hz hjy hy).
Qed.
