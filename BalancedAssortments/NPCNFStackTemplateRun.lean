import BalancedAssortments.NPCNFStackTemplate

namespace BalancedAssortments.NPCNF.StackTemplate
open NPStack
open NPStackFields (tagBits dataFields)
variable {K : Type*} [DecidableEq K]

def applyJob (regs : K → List Bool) (job : Job K) (out : List Bool) : List Bool :=
  match job with
  | .bit b => b::out
  | .field k => tagBits (regs k)++false::out

def applyJobs (regs : K → List Bool) : List (Job K) → List Bool → List Bool
  | [],out => out
  | job::jobs,out => applyJobs regs jobs (applyJob regs job out)

def jobCost (regs : K → List Bool) : Job K → ℕ
  | .bit _ => 1
  | .field k => 6*(regs k).length+4

def jobsCost (regs : K → List Bool) (jobs : List (Job K)) : ℕ := (jobs.map (jobCost regs)).sum

lemma run_suffix (jobs : List (Job K)) (inputKey : K) (regs : K → List Bool)
    (rest pre : List (Job K)) (hsplit : pre++rest=jobs) (out : List Bool) :
    Run (program jobs inputKey) (jobsCost regs rest)
      (cfg (.dispatch ⟨pre.length,by have hh := congrArg List.length hsplit; simp only [List.length_append] at hh;omega⟩) regs [] out)
      (cfg (.dispatch (Fin.last jobs.length)) regs [] (applyJobs regs rest out)) := by
  induction rest generalizing pre out with
  | nil =>
    have hp : pre=jobs := by simpa using hsplit
    subst pre
    exact Run.zero _
  | cons job rest ih =>
    have hlen : pre.length+1+rest.length=jobs.length := by
      have hh := congrArg List.length hsplit
      simp only [List.length_append,List.length_cons] at hh
      omega
    let i : Fin (jobs.length+1) := ⟨pre.length,by omega⟩
    let next : Fin (jobs.length+1) := ⟨(pre++[job]).length,by simp;omega⟩
    have hi : jobs[i.val]?=some job := by
      dsimp only [i]
      rw [← hsplit,List.getElem?_append_right (by omega)]
      simp
    have hn : advance i=next := by
      apply Fin.ext
      simp only [advance,i,next,List.length_append,List.length_cons,List.length_nil]
      omega
    have hsplit' : (pre++[job])++rest=jobs := by simpa [List.append_assoc] using hsplit
    have hr := ih (pre++[job]) hsplit' (applyJob regs job out)
    change Run (program jobs inputKey) (jobsCost regs rest)
      (cfg (.dispatch next) regs [] (applyJob regs job out)) _ at hr
    change Run (program jobs inputKey) (jobsCost regs (job::rest)) (cfg (.dispatch i) regs [] out) _
    cases job with
    | bit b =>
      have hs : Step (program jobs inputKey) (cfg (.dispatch i) regs [] out)
          (cfg (.dispatch next) regs [] (b::out)) := by
        simp [Step,successors,program,cfg,hi,hn,store]
      have hh := Run.succ hs hr
      simpa [jobsCost,jobCost,applyJobs,applyJob,Nat.add_comm] using hh
    | field k =>
      have hs : Step (program jobs inputKey) (cfg (.dispatch i) regs [] out)
          (cfg (.scan k next) regs [] out) := by
        simp [Step,successors,program,cfg,hi,hn]
      have hh := (Run.succ hs (field_run jobs inputKey k next regs out)).trans hr
      convert hh using 1 <;> simp [jobsCost,jobCost,applyJobs,applyJob] <;> omega

/-- Every fixed field template is compiled to literal Boolean push/pop code;
the exact count includes all source-preserving field copies. -/
theorem template_run (jobs : List (Job K)) (inputKey : K) (regs : K → List Bool) (out : List Bool) :
    Run (program jobs inputKey) (jobsCost regs jobs)
      (cfg (.dispatch 0) regs [] out)
      (cfg (.dispatch (Fin.last jobs.length)) regs [] (applyJobs regs jobs out)) := by
  exact run_suffix jobs inputKey regs jobs [] rfl out

lemma template_accepts (jobs : List (Job K)) (inputKey : K) (regs : K → List Bool) (out : List Bool) :
    accepts (program jobs inputKey) (cfg (.dispatch (Fin.last jobs.length)) regs [] out) := by
  simp [accepts,program,cfg]

lemma jobsCost_bound (jobs : List (Job K)) (regs : K → List Bool) (B : ℕ)
    (h : ∀ k,(regs k).length≤B) : jobsCost regs jobs≤jobs.length*(6*B+4) := by
  induction jobs with
  | nil => simp [jobsCost]
  | cons job jobs ih =>
    have hj : jobCost regs job ≤ 6*B+4 := by
      cases job with
      | bit b => simp [jobCost]
      | field k => have hh := h k; dsimp [jobCost];omega
    simp only [jobsCost,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

end BalancedAssortments.NPCNF.StackTemplate
