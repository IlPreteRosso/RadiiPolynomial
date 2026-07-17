import RadiiPolynomial.source.lpSpace.lpWeighted

open scoped BigOperators Topology
open Metric Set Filter ContinuousLinearMap RadiiPolynomial

variable {ν : PosReal}

#synth Mul (l1Weighted ν)
#synth HMul (l1Weighted ν) (l1Weighted ν) (l1Weighted ν)

#print RadiiPolynomial.lpOneAlg.instMul
