(** Federer (1969), 3.4.7, pp. 324–325:
    original null exceptional directions, Noetherian analytic
    germ rings, and unique factorization. This interface
    gathers the original assertions and their algebraic
    consequences for recursive kernel checking. Implementations
    remain behind their existing sealed interfaces. *)
From Federer Require Export EuclideanAnalyticRegularDirections
  EuclideanAnalyticGermNoetherian EuclideanAnalyticGermFactorization
  AnalyticGermFactorizationUniqueness AnalyticDistinguishedFactorReflection
  WeierstrassTransverseValue AnalyticTransversePolynomialSubring
  GaussPrimitiveScalarUnit WeierstrassTransverseInjection.
