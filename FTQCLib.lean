/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
-- Top-level entry of the FTQCLib library: imports the modules of the default build target.

import FTQCLib.Pauli.Basic
import FTQCLib.Pauli.Symplectic
import FTQCLib.Pauli.Basis
import FTQCLib.Stabilizer.Defs
import FTQCLib.Stabilizer.Codespace
import FTQCLib.Stabilizer.Normalizer
import FTQCLib.Stabilizer.Logical
import FTQCLib.Stabilizer.Dimension
import FTQCLib.Stabilizer.Error
import FTQCLib.Stabilizer.Witt
import FTQCLib.Stabilizer.WittSpanPair
import FTQCLib.Stabilizer.WittRestrictNondeg
import FTQCLib.Stabilizer.WittFinCons
import FTQCLib.Stabilizer.WittBasis
import FTQCLib.CSS.Defs
import FTQCLib.CSS.Logical
import FTQCLib.CSS.Distance
import FTQCLib.CSS.Rank
import FTQCLib.Aut.Defs
import FTQCLib.Gates.Hadamard
import FTQCLib.Gates.Phase
import FTQCLib.Gates.CNOT
import FTQCLib.Gates.CZ
import FTQCLib.Gates.Clifford
import FTQCLib.Gates.Pauli
import FTQCLib.Gates.Transvection
import FTQCLib.Gates.TransvectionAbstract
import FTQCLib.Hierarchy.Defs
import FTQCLib.Hierarchy.Descent
import FTQCLib.Hierarchy.GatePolynomials
import FTQCLib.Hierarchy.HierarchyLevel
import FTQCLib.Hierarchy.Wrapper
import FTQCLib.Hierarchy.RzHardness
import FTQCLib.Hierarchy.FuncDeriv
import FTQCLib.Hierarchy.BoolReduce
import FTQCLib.Hierarchy.BooleanMobius
import FTQCLib.Hierarchy.EffectiveLevel
import FTQCLib.Hierarchy.AffinePushforward
import FTQCLib.Gates.CCNOT
import FTQCLib.Stabilizer.PauliCondition
import FTQCLib.Stabilizer.GottesmanKnill
import FTQCLib.Codes.Transversal
import FTQCLib.Codes.CSSCnot
import FTQCLib.Codes.AJO
import FTQCLib.Codes.AJOOverlap
import FTQCLib.Codes.AJOMain
import FTQCLib.Codes.AJOLattice
import FTQCLib.Codes.AJOGeneral
import FTQCLib.Codes.AJOClosure
import FTQCLib.Codes.AJOLogical
import FTQCLib.Hilbert.QubitSpace
import FTQCLib.Hilbert.Codespace
import FTQCLib.Hilbert.Diagonal
import FTQCLib.Hilbert.PauliOp
import FTQCLib.Hilbert.PauliProduct
import FTQCLib.Hilbert.PauliEquiv
import FTQCLib.Hilbert.DiagonalEquiv
import FTQCLib.Hilbert.CGK
import FTQCLib.Hilbert.Hierarchy
import FTQCLib.Hilbert.HierarchyDyadic
import FTQCLib.Hilbert.CliffordSymplectic
import FTQCLib.Hilbert.AffineSymplectic
import FTQCLib.Hilbert.SymplecticGeneration
import FTQCLib.Hilbert.GateLifts
import FTQCLib.Hilbert.AffineSymplecticGroup
import FTQCLib.Hilbert.CliffordSplitN1
import FTQCLib.Hilbert.Inner
import FTQCLib.Hilbert.StabilizerState
import FTQCLib.Hilbert.BornCollapse
import FTQCLib.Hilbert.Separation
import FTQCLib.Hilbert.StabilizerEquiv
import FTQCLib.Hilbert.LemSpan
import FTQCLib.Hilbert.StabilizerTheory
import FTQCLib.Hilbert.MeasurementCollapse
import FTQCLib.Hilbert.AccuracyChecks
import FTQCLib.Stabilizer.KochenSpecker
import FTQCLib.Hilbert.AJOOperator
import FTQCLib.Hilbert.CGKForward
import FTQCLib.Hilbert.CGKReverseIteration
import FTQCLib.Hilbert.CGKReverseDyadic
import FTQCLib.Hilbert.CGKReverse
import FTQCLib.Hilbert.CGKReverseAnchor
import FTQCLib.Hilbert.CGKReverseLevel3
import FTQCLib.Hilbert.CGKReverseAssembly
import FTQCLib.Hilbert.CGKReverseGeneral
import FTQCLib.Hilbert.CGKReverseVanish
import FTQCLib.Hilbert.CGKReverseStrict
import FTQCLib.Hilbert.CGKReverseTightLevel
import FTQCLib.Hilbert.ProjectiveHierarchy
import FTQCLib.Hilbert.ProjectiveStrictLevel
import FTQCLib.Hilbert.CGKSharpForward
import FTQCLib.Hilbert.CGKTwoSided
import FTQCLib.Hilbert.CGKGateTests
import FTQCLib.Hilbert.CGKExactness
import FTQCLib.Hilbert.CGKGroupStructure
import FTQCLib.Hilbert.CGKCoverage
-- Kernel frame — operational / difference route
import FTQCLib.Hierarchy.FrameMoves
import FTQCLib.Hierarchy.FrameExponent
import FTQCLib.Hilbert.FrameKernel
import FTQCLib.Hilbert.FrameRepresentation
import FTQCLib.Hilbert.FrameDescent
import FTQCLib.Hilbert.FrameDescentReverse
import FTQCLib.Hilbert.FrameDescentReverseDischarge
import FTQCLib.Hilbert.FrameTests
import FTQCLib.Hilbert.FrameBridge
import FTQCLib.Hilbert.FrameBridgeAmplitude
import FTQCLib.Hilbert.FrameBridgeAmplitudeCore
import FTQCLib.Hilbert.FrameBridgeAmplitudeQuad
import FTQCLib.Hilbert.ToffoliFrame

-- Examples — physical CCZ decomposition, two frames
import FTQCLib.Examples.CCZ.OperatorFrame
import FTQCLib.Examples.CCZ.KernelFrame

-- Bridge — the Klein-word chart into the ECCLib Delsarte-scheme layer
import FTQCLib.Bridge.PauliKlein
import FTQCLib.Bridge.PauliKleinCheck
