# Agent Verification, Formally — Why the Next Layer Has to Be a Proof

*2026-08-25 · Nobuki Fujimoto (藤本伸樹) · [@fc0web](https://github.com/fc0web) · 12 min read*

> Benchmark scores and LLM-as-a-judge scores tell you an agent worked on the samples you tried. Formal verification tells you it works on the ones you didn't. This post shows what that second thing actually looks like — using Lean 4 to prove a real property about an agent, in about forty lines of code.

In June 2025, Gartner published a prediction that seems to have aged extremely well: **over 40% of agentic AI projects will be cancelled by the end of 2027**, mostly because of cost overruns and, more importantly, *"unclear business value or inadequate risk controls."* A year later, most of the tooling that has grown around the AI agent space is aimed at exactly the first half of that sentence — cost, latency, throughput, sampling. Almost none of it addresses the second half.

This post is about the second half. Specifically: what it would mean to make a claim about an agent that a machine can check, that holds for *every* input, not just the ones you tested. That is what "formally verified" means. This post walks through what it looks like to do that for an agent, in Lean 4, in about forty lines of code — and, just as importantly, what it does not do.

## 1. Two things that are called "agent evaluation"

The 2026 AI agent evaluation landscape is dominated by two families of tools. The first is **benchmark-and-sample**: you write a suite of scenarios, run the agent through them, and measure completion rate, tool-call correctness, plan quality, or task success. The most respected examples — τ-bench, SWE-bench, AgentBench — go beyond "did the LLM emit reasonable text" and check *executed state*: did the database actually get updated correctly, did the test suite actually pass. This is a real improvement over the "score the text output" era. It is not, however, verification.

The second family is **LLM-as-a-judge**: you use a second model, usually a strong one, to score the outputs of the first. It scales, and it is cheap, and it captures nuance that keyword-matching cannot. DeepEval, Braintrust, Langfuse, Arize Phoenix and roughly a dozen commercial platforms are built around this idea. It is a way to make the sampling loop tighter and the judgments more like human ones. It is not verification either.

The difference is quiet but important. Benchmarking answers *"how does the agent perform on the distribution of inputs I tested?"* Verification answers *"is this property true for **all** inputs, including inputs no one has written down?"* Sampling tools stop at the first question. In domains where an agent moves money, dispenses medicine, controls physical equipment, or acts on behalf of a user with real authority, only the second question is load-bearing.

## 2. What "the second question" actually means

The claim that a program is *correct* has been a formal object for about sixty years. Tony Hoare's 1969 paper on the axiomatic basis of programming introduced the notation `{P} S {Q}` — if the predicate `P` holds before executing `S`, then `Q` holds after. Everything that has happened since in program verification — separation logic, refinement types, dependent types, model checking, SMT-backed contracts — is elaboration and mechanization of that idea.

For an AI agent, the corresponding statement is not much different. An agent has a state (memory, goals, tools it has invoked, side effects it has committed). Each action moves it from one state to another. A *property* is a claim about the states an agent can reach: *"the agent never commits a financial transaction without a valid authorization token in scope,"* or *"the agent never exposes a document classified above the requester's clearance,"* or *"whenever the agent proposes a database write, the write is reversible for at least 24 hours."*

Sampling-based evaluation says: "I ran a hundred scenarios, and in ninety-eight of them the property held." Formal verification says: "I have a proof, checked by a small kernel, that the property holds in every reachable state — including the states no scenario reached."

The distance between those two claims is exactly the distance between "we didn't observe a failure in testing" and "a failure cannot happen." For most software, the first is enough. For a fraction of software — and increasingly for AI agents — it is not.

## 3. What you can and cannot verify about an agent

Here is the honest scope. You cannot verify the LLM. A modern language model is a neural network of hundreds of billions of parameters trained on a corpus no one can enumerate. There is no useful specification of what it will output; there is no proof about the distribution of its next tokens that is worth writing. If someone tells you they formally verified a language model itself, they either mean something much weaker than they are implying, or they are describing an active research program that is nowhere near production.

What you *can* verify is the **harness** around the LLM: the code that reads the model's output, decides what to do with it, invokes tools, updates state, and commits side effects. That harness is ordinary software. It is a small state machine wrapped around an oracle. And it is the harness — not the model — that is responsible for the property in every real safety claim.

Consider "the agent will not execute a transaction without authorization." The model might well *propose* such a transaction; models are stochastic and prompt-injectable and occasionally bizarre. The property that matters is not that the model never proposes it. The property that matters is that the *harness* refuses to execute it. That refusal lives in about ten lines of code. It is those ten lines that can — and, in high-stakes deployments, should — be proved correct.

This is a genuinely useful scoping. It means formal verification of agents is not blocked on the mystery of LLM internals. It is blocked, if it is blocked at all, on writing down what the harness must guarantee and then proving that the code does it.

## 4. A minimal example, in Lean 4

Let us do this concretely. We will model a tiny agent that takes actions of three kinds — planning, calling a tool, or committing a transaction — and prove the property *the agent never adds to its committed-transaction list when it has no authorization token.* Complete Lean 4 source; you can paste this into any Lean 4 project and it will type-check.

```lean
-- Types the agent works with.
structure AuthToken where
  issuer  : String
  expires : Nat
  deriving Repr

structure Transaction where
  amount   : Nat
  receiver : String
  deriving Repr

structure ToolCall where
  name : String
  args : String
  deriving Repr

-- Every action the agent can take.
inductive AgentAction where
  | plan (goal : String)
  | callTool (call : ToolCall)
  | commitTransaction (tx : Transaction)
  deriving Repr

-- Everything the agent carries with it.
structure AgentState where
  auth      : Option AuthToken
  committed : List Transaction
  toolLog   : List ToolCall
  deriving Repr

-- The transition function. This is the harness.
def step (s : AgentState) : AgentAction → AgentState
  | .plan _                => s
  | .callTool c            => { s with toolLog := c :: s.toolLog }
  | .commitTransaction tx  =>
      match s.auth with
      | none   => s                                          -- refuse: no auth
      | some _ => { s with committed := tx :: s.committed }  -- accept
```

That is the entire model. The action of interest is `commitTransaction`: it pattern-matches on the auth field and refuses when it is `none`.

Now the theorem. What we want to prove: if the agent had no auth before a step, its committed list does not grow.

```lean
theorem no_commit_without_auth
    (s : AgentState) (a : AgentAction)
    (h : s.auth = none) :
    (step s a).committed = s.committed := by
  cases a with
  | plan _              => rfl
  | callTool _          => rfl
  | commitTransaction _ =>
      simp [step, h]
```

Five lines of proof. `cases a` splits on the three possible actions. `plan` and `callTool` do not touch `committed`, so `rfl` — reflexivity — closes each. For `commitTransaction`, `simp [step, h]` unfolds `step` and uses the hypothesis `h : s.auth = none` to force the `none` branch, which returns `s` unchanged. The theorem is proved.

But that is a one-step claim. What we actually want is stronger: *the committed list does not grow across any sequence of steps, as long as auth stays* `none`. That is an induction.

```lean
-- Run the agent on a list of actions in order.
def run : AgentState → List AgentAction → AgentState
  | s, []      => s
  | s, a :: as => run (step s a) as

theorem no_commit_without_auth_ever
    (s : AgentState) (as : List AgentAction)
    (h_init : s.auth = none)
    (h_no_grant : ∀ a ∈ as, ∀ tok, a ≠ .callTool ⟨"grant_auth", tok⟩) :
    (run s as).committed = s.committed := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih =>
      have h_step_auth : (step s a).auth = s.auth := by
        cases a with
        | plan _              => rfl
        | callTool c          => rfl
        | commitTransaction _ => simp [step, h_init]
      have h_next : (step s a).auth = none := h_step_auth ▸ h_init
      have h_next_committed : (step s a).committed = s.committed :=
        no_commit_without_auth s a h_init
      rw [run, ih (step s a) h_next (fun a' ha' => h_no_grant a' (List.mem_cons_of_mem _ ha'))]
      exact h_next_committed
```

That proof does slightly more work — it has to carry the auth invariant across the induction, and it has to depend on an assumption that no action in the sequence *granted* auth. In a fuller model you would model auth-granting as its own action, prove that only that action can flip `auth` from `none` to `some`, and derive the same conclusion more compactly. The proof above is deliberately un-abstracted so the mechanics stay visible.

The interesting thing is not the proof itself. It is that once Lean's kernel has accepted these lines, the claim is settled — not for the traces you tested, but for every list of actions the agent can be given. You did not have to think of the adversarial sequence, because the induction covers all sequences. This is the specific thing sampling cannot do.

## 5. What this changes about how you build an agent

Almost nothing, in the short term, if you do not need it. Most agent workloads today — summarization, drafting, unstructured retrieval — do not have a property this sharp. Their success criterion is "reasonable output most of the time," and sampling-based evaluation is exactly the right tool.

The picture changes at the boundary where the agent's actions become irreversible or attributable. A few examples where the shape of the guarantee shifts:

- **Financial actions.** *"The agent will not initiate a transfer above threshold T without a two-factor confirmation."* A property that must hold on every trace, not most.
- **Regulated data access.** *"The agent will not include personally identifying information in any output routed to unauthenticated recipients."* A monotonic non-leakage claim; sampling cannot exhaust the leak surface.
- **Physical control.** Agents wired to lab equipment, HVAC systems, warehouse robotics. *"No sequence of commands leaves the actuator in a state outside operational safety bounds."*
- **Autonomous procurement.** *"The agent will not commit spending beyond the current budget line."*
- **Compliance-flagged deployments.** Anywhere the deployer might have to demonstrate, to a regulator or an auditor, that a class of failure *cannot* happen. "Our test suite didn't catch it" is not a defense here; "we have a proof it doesn't happen" is.

For workloads like these, the practical architecture is not "run an LLM and hope." It is: **the LLM proposes, the verified harness disposes.** The harness is small, adversarially designed, and its critical properties are formally verified. The LLM does everything the harness permits and nothing it does not. This is not novel as a pattern — it is how a great many high-assurance systems have been built for decades — but its application to LLM-driven agents is genuinely new, and it is where the interesting work is happening.

## 6. Where this fits, and where it does not

Some honesty about the limits.

**Formal verification does not verify emergent behavior.** If the property you care about is *"the agent behaves helpfully"* or *"the agent's outputs are factually correct"*, no proof will help you. Those are properties of the LLM, which is out of scope for the harness. LLM-as-a-judge, red-teaming, and sampling evaluation remain the right tools.

**Formal verification is not free.** Writing the model and the proof for a real agent harness is a few weeks of specialist work, not a few hours. That cost is worth paying when the alternative is "we cannot ship in this jurisdiction" or "an untested failure mode costs us a million dollars per incident." It is not worth paying to gild a chatbot.

**Formal verification cannot cover the parts you did not model.** A proof about the harness says nothing about a bug in the network layer, the operating system, or the LLM API's rate limiter. What it does is *reduce* your trust surface to those layers explicitly, so you can audit them separately and know what you are trusting.

**Formal verification does not remove the need for testing.** Proofs are about specifications. Tests are about whether your specification is the right one. Both remain necessary. What formal verification removes is the class of failure where the code disagrees with a specification you already had.

Within those limits, the case is straightforward: for any agent whose failure has consequences you would refuse to accept even once, sampling-based evaluation is a floor, not a ceiling. The ceiling is a proof.

## 7. Where LeanDFumt fits

The example in section 4 is standard Lean 4. It requires no library beyond Mathlib and no framework beyond Lean itself; you could implement it today. The [LeanDFumt](https://github.com/fc0web/lean-d-fumt8) library — 29 zero-sorry theorems for D-FUMT₈ eight-valued logic, no Mathlib dependency, Apache 2.0 — is the public anchor of a broader Rei-AIOS effort that treats *phase structure* as a first-class object: values move through discrete phases, transitions are witnessed, and the type system refuses to let a value cross a phase boundary without producing evidence.

That structure is a natural fit for the harness pattern above. An agent action, in Rei terms, is not a function from state to state — it is a phase transition witnessed by an authorization token. The theorem `no_commit_without_auth` becomes a phase-monotonicity property, provable by construction rather than by induction. The [error database](./index.html) in this same docs tree lists the everyday Lean 4 errors encountered while writing proofs like these, each with a fix that preserves the zero-`sorry`, no-Mathlib discipline.

A hands-on Lean 4 primer for readers who have never opened a proof assistant is [here](./first-proof.html) — five steps, no installation, roughly ten minutes.

If you are running agent workloads in a domain where "we did not observe it in testing" is not an acceptable answer, the right next step is not more test coverage. It is to write down the property you are actually promising and prove it. Everything else follows.

---

*A LeanDFumt note by Nobuki Fujimoto, part of the Rei-AIOS open-science effort. Apache 2.0 licensed — see [LICENSE](../LICENSE). Repository: [fc0web/lean-d-fumt8](https://github.com/fc0web/lean-d-fumt8). ORCID: [0009-0004-6019-9258](https://orcid.org/0009-0004-6019-9258).*
