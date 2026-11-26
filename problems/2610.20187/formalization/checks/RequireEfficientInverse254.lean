import EfficientSpectralClip254
import EfficientInverseCertificate254
import HistoryBitCertificate254
import RationalRunMasterWork254
import ExactWorkspace254
import ExactProjectionInterface254
import MasterWorkspace254
open Matrix Paper254
#print axioms Paper254.efficientInverse_correct
#print axioms Paper254.efficientGeneralInverse_correct
#print axioms Paper254.efficientNewton_eq
#print axioms Paper254.efficientCertifiedMatrixSqrt_error
#print axioms Paper254.efficientSpectralClip_interval
#print axioms Paper254.countedGeneralInverse_certificate
#print axioms Paper254.chargedHistoryStep_certificate
#print axioms Paper254.RationalRunEncodingSetup.master_run_certificate
#print axioms Paper254.RationalRunEncodingSetup.total_master_charge
#print axioms Paper254.countedExactRound_weights
#print axioms Paper254.countedExactRound_histories
#print axioms Paper254.exact_curved_total_cost
#print axioms Paper254.profiledExactHistory_dense_workspace
#print axioms Paper254.profiledMasterUpdate_program
#print axioms Paper254.profiledMasterUpdate_workspace
#print axioms Paper254.rotatedPrecision_map_eq
#print axioms Paper254.exact_metric_minimizer_unique
#eval (let A : Matrix (Fin 2) (Fin 2) ℚ := !![1,2;3,5]
       let rows := efficientGeneralInverseRows A
       decide (rationalMatrixOfRows rows=!![-5,2;3,-1]))
#eval (let A : Matrix (Fin 6) (Fin 6) ℚ := fun i j=>if i=j then 2 else if i<j then 1 else 0
       let rows := efficientGeneralInverseRows A
       decide (A*rationalMatrixOfRows rows=1))
#eval (let A : Matrix (Fin 3) (Fin 3) ℚ := !![1,2,0;0,3,1;1,0,2]
       let result := countedGeneralInverse A
       decide (A*result.1=1 ∧ result.2≤12*3^3))
#eval (let live : Finset (Fin 3) := Finset.univ
       let result := countedMasterUpdate 2 1 live live (fun _=>1/3)
         (fun i=>(i.val:ℚ)/4) (fun _=>1/3) (1/4)
       decide ((result.1.map Prod.snd).sum=1 ∧ result.2=3*(3*(2+7)+7)+3*(3*(2+7)+13)+2*2+4))
#eval (let live : Finset (Fin 3) := Finset.univ
       let profiled := profiledMasterUpdate 2 1 live live (fun _=>1/3)
         (fun i=>(i.val:ℚ)/4) (fun _=>1/3) (1/4)
       let counted := countedMasterUpdate 2 1 live live (fun _=>1/3)
         (fun i=>(i.val:ℚ)/4) (fun _=>1/3) (1/4)
       decide (profiled.1=counted ∧ profiled.2≤24*(3+3+2+1)))
#eval (let A : Matrix (Fin 2) (Fin 2) ℚ := !![2,1;1,2]
       let rows := efficientNewtonRows (matrixSqrtPrecision 1 1 2) A ((2:ℚ) • 1)
         (matrixSqrtIterations 1 1 2)
       let X := rationalMatrixOfRows rows
       decide (∀ i j, |(X*X-A) i j|≤(1/100:ℚ)))
#eval (let A : Matrix (Fin 2) (Fin 2) ℚ := !![-1,0;0,3]
       let rows := efficientSpectralClipRows 1 3 3 (1/4) 0 2 A
       let X := rationalMatrixOfRows rows
       decide (|X 0 0|≤(1/10:ℚ) ∧ |X 1 1-2|≤(1/10:ℚ) ∧ X 0 1=0 ∧ X 1 0=0))
