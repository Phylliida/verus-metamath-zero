//! Phase 0 spike: Emit a .mmb proof of `id: a -> a` in propositional logic.
//!
//! Proves identity using the classic Hilbert proof:
//!   ax_mp (ax_mp ax_2 ax_1) (ax_1 a (not a))

use mm0b_parser::{Arg, Mm0Writer, ProofCmd, SortData, UnifyCmd, cmd::STMT_SORT, write_cmd_bytes};
use mm0_util::{SortId, TermId, ThmId};
use std::fs::File;
use std::io::{self, Write};

const SORT_WFF: SortId = SortId(0);
const TERM_IMP: TermId = TermId(0);
const TERM_NOT: TermId = TermId(1);
const THM_AX1: ThmId = ThmId(0);
const THM_AX2: ThmId = ThmId(1);
#[allow(dead_code)]
const THM_AX3: ThmId = ThmId(2);
const THM_AX_MP: ThmId = ThmId(3);

fn arg_sort(sort: SortId) -> Arg {
    Arg::new_of_sort(sort.0)
}

fn main() -> io::Result<()> {
    let mut w: Mm0Writer<Vec<u8>> = Mm0Writer::new(Vec::new());
    let wff = arg_sort(SORT_WFF);

    // ── Sort 0: wff (provable=0x04) ──
    w.add_sort(Some("wff"), SortData(0x04));

    // ── Term 0: imp (a b: wff) -> wff ──
    w.add_term(Some("imp"), &[wff, wff], wff)?;

    // ── Term 1: not (a: wff) -> wff ──
    w.add_term(Some("not"), &[wff], wff)?;

    // ── Axiom 0: ax_1 (a b: wff): a -> b -> a ──
    // Conclusion: imp(a, imp(b, a))
    {
        let mut thm = w.add_axiom(Some("ax_1"), &[wff, wff]);
        let u = thm.unify();
        UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;
        UnifyCmd::Ref(0).write_to(u)?;
        UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;
        UnifyCmd::Ref(1).write_to(u)?;
        UnifyCmd::Ref(0).write_to(u)?;
        thm.finish()?;
    }

    // ── Axiom 1: ax_2 (a b c: wff): (a->b->c) -> (a->b) -> (a->c) ──
    {
        let mut thm = w.add_axiom(Some("ax_2"), &[wff, wff, wff]);
        let u = thm.unify();
        // imp(imp(a, imp(b, c)), imp(imp(a, b), imp(a, c)))
        UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;  // outer imp
        UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;  //   imp(a, imp(b,c))
        UnifyCmd::Ref(0).write_to(u)?;                                //     a
        UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;  //     imp(b, c)
        UnifyCmd::Ref(1).write_to(u)?;                                //       b
        UnifyCmd::Ref(2).write_to(u)?;                                //       c
        UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;  //   imp(imp(a,b), imp(a,c))
        UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;  //     imp(a, b)
        UnifyCmd::Ref(0).write_to(u)?;                                //       a
        UnifyCmd::Ref(1).write_to(u)?;                                //       b
        UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;  //     imp(a, c)
        UnifyCmd::Ref(0).write_to(u)?;                                //       a
        UnifyCmd::Ref(2).write_to(u)?;                                //       c
        thm.finish()?;
    }

    // ── Axiom 2: ax_3 (a b: wff): (~a -> ~b) -> (b -> a) ──
    {
        let mut thm = w.add_axiom(Some("ax_3"), &[wff, wff]);
        let u = thm.unify();
        // imp(imp(not(a), not(b)), imp(b, a))
        UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;
        UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;
        UnifyCmd::Term { tid: TERM_NOT, save: false }.write_to(u)?;
        UnifyCmd::Ref(0).write_to(u)?;
        UnifyCmd::Term { tid: TERM_NOT, save: false }.write_to(u)?;
        UnifyCmd::Ref(1).write_to(u)?;
        UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;
        UnifyCmd::Ref(1).write_to(u)?;
        UnifyCmd::Ref(0).write_to(u)?;
        thm.finish()?;
    }

    // ── Axiom 3: ax_mp (a b: wff): a -> b > a > b ──
    // 2 hypotheses: imp(a,b), a. Conclusion: b
    {
        let mut thm = w.add_axiom(Some("ax_mp"), &[wff, wff]);
        let u = thm.unify();
        // UHyp for hyp 1: imp(a, b)
        UnifyCmd::Hyp.write_to(u)?;
        UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;
        UnifyCmd::Ref(0).write_to(u)?;
        UnifyCmd::Ref(1).write_to(u)?;
        // UHyp for hyp 2: a
        UnifyCmd::Hyp.write_to(u)?;
        UnifyCmd::Ref(0).write_to(u)?;
        // Conclusion: b
        UnifyCmd::Ref(1).write_to(u)?;
        thm.finish()?;
    }

    // ══════════════════════════════════════════════════════════════════
    // Theorem 4: id (a: wff): a -> a
    //
    // Proof: ax_mp (ax_mp ax_2 ax_1) (ax_1 a (not a))
    //
    // The proof term expanded:
    //   Let N = not(a), M = imp(N, a)
    //
    //   inner_ax1 = ax_1(a, M):   |- imp(a, imp(M, a))
    //   inner_ax2 = ax_2(a, M, a): |- imp(imp(a,imp(M,a)), imp(imp(a,M), imp(a,a)))
    //   inner_mp  = ax_mp(imp(a,imp(M,a)), imp(imp(a,M),imp(a,a))):
    //               hyps: inner_ax2, inner_ax1
    //               |- imp(imp(a, M), imp(a, a))
    //
    //   outer_ax1 = ax_1(a, N):   |- imp(a, imp(N, a))  =  |- imp(a, M)
    //   outer_mp  = ax_mp(imp(a,M), imp(a,a)):
    //               hyps: inner_mp, outer_ax1
    //               |- imp(a, a)
    //
    // MMB proof stack trace:
    //   Heap starts: [a]  (index 0)
    //
    //   We build bottom-up: hypotheses go below on the stack,
    //   then args and conclusion on top, then Thm pops everything.
    // ══════════════════════════════════════════════════════════════════
    {
        let mut thm = w.add_thm(false, Some("id"), &[wff]);

        // Unify stream: conclusion = imp(a, a)
        UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(thm.unify())?;
        UnifyCmd::Ref(0).write_to(thm.unify())?;
        UnifyCmd::Ref(0).write_to(thm.unify())?;

        let p = thm.proof();

        // Heap: [a] (idx 0)
        // We'll build helper expressions and save them for reuse.

        // ── Build not(a) → heap[1] ──
        ProofCmd::Ref(0).write_to(p)?;                              // push a
        ProofCmd::Term { tid: TERM_NOT, save: true }.write_to(p)?;  // not(a) → heap[1]
        // Stack: [not(a)]

        // ── Build imp(not(a), a) = M → heap[2] ──
        ProofCmd::Ref(1).write_to(p)?;                              // push not(a)
        ProofCmd::Ref(0).write_to(p)?;                              // push a
        ProofCmd::Term { tid: TERM_IMP, save: true }.write_to(p)?;  // imp(not(a), a) → heap[2]
        // Stack: [not(a), M]  (not(a) leftover from before? No — TermSave pops args)
        // Actually: after TermSave for not(a), stack = [not(a)]
        // Then Ref(1), Ref(0) pushes not(a) and a → [not(a), not(a), a]
        // Then TermSave for imp pops 2, pushes imp(not(a), a) → [not(a), imp(not(a), a)]
        // Hmm, there's a leftover not(a). Let me re-trace.
        //
        // After "Build not(a)":
        //   TermSave(not) pops 1 arg (a), pushes not(a) and saves to heap
        //   Stack: [not(a)]
        //
        // After "Build M":
        //   Ref(1) pushes not(a) from heap → Stack: [not(a), not(a)]
        //   Ref(0) pushes a from heap     → Stack: [not(a), not(a), a]
        //   TermSave(imp) pops 2 (not(a), a), pushes imp(not(a), a), saves to heap
        //   Stack: [not(a), M]
        //
        // I have a stray not(a) on the stack. I need to be more careful.
        // The issue is that after building not(a), it's still on the stack.
        // I should only build things I need, or clear them.
        //
        // Actually, I can just use Save to save not(a) to the heap without
        // leaving it on the stack. But Save does leave it on the stack...
        // TermSave also leaves it on the stack.
        //
        // The trick: I need to plan the stack layout so that everything
        // left on the stack is consumed by a later Thm application.
        //
        // Let me take a completely different approach: build everything in the
        // order that ax_mp needs it on the stack.

        // Let me restart with a clean approach. The proof buffer is already
        // partially written, which is a problem. Let me create the Mm0Writer
        // from scratch and do it right.

        // Actually — I realize I can't easily undo what I've written.
        // The ThmBuilder writes to internal buffers of the Mm0Writer.
        // Let me just abort and redo the whole file.
        drop(thm);
        drop(w);
        return build_correct();
    }
}

fn build_correct() -> io::Result<()> {
    // Pre-write STMT_SORT to proof stream — Mm0Writer::add_sort doesn't do this.
    let mut proof_buf = Vec::new();
    write_cmd_bytes(&mut proof_buf, STMT_SORT, &[])?;
    let mut w: Mm0Writer<Vec<u8>> = Mm0Writer::new(proof_buf);
    let wff = arg_sort(SORT_WFF);

    // Sort 0: wff (provable)
    w.add_sort(Some("wff"), SortData(0x04));
    // Term 0: imp
    w.add_term(Some("imp"), &[wff, wff], wff)?;
    // Term 1: not
    w.add_term(Some("not"), &[wff], wff)?;

    // Axiom 0: ax_1 (a b: wff): a -> b -> a
    // Proof stream must construct conclusion expr: imp(a, imp(b, a))
    {
        let mut t = w.add_axiom(Some("ax_1"), &[wff, wff]);
        write_unify_imp_a_imp_b_a(t.unify())?;
        let p = t.proof();
        // Heap: [a(0), b(1)]
        ProofCmd::Ref(0).write_to(p)?;                              // [a]
        ProofCmd::Ref(1).write_to(p)?;                              // [a, b]
        ProofCmd::Ref(0).write_to(p)?;                              // [a, b, a]
        ProofCmd::Term { tid: TERM_IMP, save: false }.write_to(p)?; // [a, imp(b, a)]
        ProofCmd::Term { tid: TERM_IMP, save: false }.write_to(p)?; // [imp(a, imp(b, a))]
        t.finish()?;
    }

    // Axiom 1: ax_2 (a b c: wff): (a->b->c) -> (a->b) -> (a->c)
    {
        let mut t = w.add_axiom(Some("ax_2"), &[wff, wff, wff]);
        write_unify_ax2(t.unify())?;
        let p = t.proof();
        // Heap: [a(0), b(1), c(2)]
        // Build: imp(imp(a, imp(b, c)), imp(imp(a, b), imp(a, c)))
        // LHS: imp(a, imp(b, c))
        ProofCmd::Ref(0).write_to(p)?;                              // a
        ProofCmd::Ref(1).write_to(p)?;                              // b
        ProofCmd::Ref(2).write_to(p)?;                              // c
        ProofCmd::Term { tid: TERM_IMP, save: false }.write_to(p)?; // imp(b, c)
        ProofCmd::Term { tid: TERM_IMP, save: false }.write_to(p)?; // imp(a, imp(b, c))
        // RHS: imp(imp(a, b), imp(a, c))
        ProofCmd::Ref(0).write_to(p)?;                              // a
        ProofCmd::Ref(1).write_to(p)?;                              // b
        ProofCmd::Term { tid: TERM_IMP, save: false }.write_to(p)?; // imp(a, b)
        ProofCmd::Ref(0).write_to(p)?;                              // a
        ProofCmd::Ref(2).write_to(p)?;                              // c
        ProofCmd::Term { tid: TERM_IMP, save: false }.write_to(p)?; // imp(a, c)
        ProofCmd::Term { tid: TERM_IMP, save: false }.write_to(p)?; // imp(imp(a,b), imp(a,c))
        // Outer: imp(LHS, RHS)
        ProofCmd::Term { tid: TERM_IMP, save: false }.write_to(p)?; // full conclusion
        t.finish()?;
    }

    // Axiom 2: ax_3 (a b: wff): (~a -> ~b) -> (b -> a)
    {
        let mut t = w.add_axiom(Some("ax_3"), &[wff, wff]);
        write_unify_ax3(t.unify())?;
        let p = t.proof();
        // Heap: [a(0), b(1)]
        // Build: imp(imp(not(a), not(b)), imp(b, a))
        ProofCmd::Ref(0).write_to(p)?;
        ProofCmd::Term { tid: TERM_NOT, save: false }.write_to(p)?; // not(a)
        ProofCmd::Ref(1).write_to(p)?;
        ProofCmd::Term { tid: TERM_NOT, save: false }.write_to(p)?; // not(b)
        ProofCmd::Term { tid: TERM_IMP, save: false }.write_to(p)?; // imp(not(a), not(b))
        ProofCmd::Ref(1).write_to(p)?;                              // b
        ProofCmd::Ref(0).write_to(p)?;                              // a
        ProofCmd::Term { tid: TERM_IMP, save: false }.write_to(p)?; // imp(b, a)
        ProofCmd::Term { tid: TERM_IMP, save: false }.write_to(p)?; // full conclusion
        t.finish()?;
    }

    // Axiom 3: ax_mp (a b: wff): a -> b > a > b
    // Has 2 hypotheses: imp(a,b) and a. Conclusion: b.
    // Push hyps in .mm0 order (hyp1 first). HS LIFO means UHyp gets hyp2 first,
    // which matches the parser's reversed linked list.
    {
        let mut t = w.add_axiom(Some("ax_mp"), &[wff, wff]);
        write_unify_ax_mp(t.unify())?;
        let p = t.proof();
        // Heap: [a(0), b(1)]
        // Build hyp 1 FIRST (deeper on HS): imp(a, b)
        ProofCmd::Ref(0).write_to(p)?;                              // a
        ProofCmd::Ref(1).write_to(p)?;                              // b
        ProofCmd::Term { tid: TERM_IMP, save: false }.write_to(p)?; // imp(a, b)
        ProofCmd::Hyp.write_to(p)?;                                 // HS=[imp(a,b)], heap[2]=|- imp(a,b)
        // Build hyp 2 SECOND (on top of HS): a
        ProofCmd::Ref(0).write_to(p)?;                              // a
        ProofCmd::Hyp.write_to(p)?;                                 // HS=[imp(a,b), a], heap[3]=|- a
        // Build conclusion: b
        ProofCmd::Ref(1).write_to(p)?;                              // b
        t.finish()?;
    }

    // Theorem 4: id (a: wff): a -> a
    {
        let mut t = w.add_thm(false, Some("id"), &[wff]);

        // Unify: conclusion = imp(a, a)
        let u = t.unify();
        UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;
        UnifyCmd::Ref(0).write_to(u)?;
        UnifyCmd::Ref(0).write_to(u)?;

        // Proof stream
        write_proof_id(t.proof())?;

        t.finish()?;
    }

    // Write output
    let mut out = File::create("proplog.mmb")?;
    w.finish(&mut out)?;
    println!("Wrote proplog.mmb");
    Ok(())
}

// ── Unify helpers ──

fn write_unify_imp_a_imp_b_a(u: &mut impl Write) -> io::Result<()> {
    // imp(a, imp(b, a))
    UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;
    UnifyCmd::Ref(0).write_to(u)?;
    UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;
    UnifyCmd::Ref(1).write_to(u)?;
    UnifyCmd::Ref(0).write_to(u)
}

fn write_unify_ax2(u: &mut impl Write) -> io::Result<()> {
    // imp(imp(a, imp(b, c)), imp(imp(a, b), imp(a, c)))
    UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;
    UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;
    UnifyCmd::Ref(0).write_to(u)?;
    UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;
    UnifyCmd::Ref(1).write_to(u)?;
    UnifyCmd::Ref(2).write_to(u)?;
    UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;
    UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;
    UnifyCmd::Ref(0).write_to(u)?;
    UnifyCmd::Ref(1).write_to(u)?;
    UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;
    UnifyCmd::Ref(0).write_to(u)?;
    UnifyCmd::Ref(2).write_to(u)
}

fn write_unify_ax3(u: &mut impl Write) -> io::Result<()> {
    // imp(imp(not(a), not(b)), imp(b, a))
    UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;
    UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;
    UnifyCmd::Term { tid: TERM_NOT, save: false }.write_to(u)?;
    UnifyCmd::Ref(0).write_to(u)?;
    UnifyCmd::Term { tid: TERM_NOT, save: false }.write_to(u)?;
    UnifyCmd::Ref(1).write_to(u)?;
    UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;
    UnifyCmd::Ref(1).write_to(u)?;
    UnifyCmd::Ref(0).write_to(u)
}

fn write_unify_ax_mp(u: &mut impl Write) -> io::Result<()> {
    // Conclusion FIRST (ustack starts with [concl], must be consumed before UHyp).
    // Then hypotheses in REVERSE .mm0 order (parser builds reversed linked list).
    // .mm0: $ a -> b $ > $ a $ > $ b $
    //   hyp1 = imp(a,b), hyp2 = a, conclusion = b
    // Parser linked list: hyp2 → hyp1 → nil (reversed)
    // So: UHyp 1 gets hyp2(a), UHyp 2 gets hyp1(imp(a,b))
    //
    // Conclusion: b
    UnifyCmd::Ref(1).write_to(u)?;
    // Hyp 2 (a) — popped FIRST from both parser list and verifier HS
    UnifyCmd::Hyp.write_to(u)?;
    UnifyCmd::Ref(0).write_to(u)?;
    // Hyp 1 (imp(a, b)) — popped SECOND
    UnifyCmd::Hyp.write_to(u)?;
    UnifyCmd::Term { tid: TERM_IMP, save: false }.write_to(u)?;
    UnifyCmd::Ref(0).write_to(u)?;
    UnifyCmd::Ref(1).write_to(u)
}

/// Emit the proof of `id: a -> a` using ax_1, ax_2, ax_mp.
///
/// Let N = not(a), M = imp(N, a).
///
/// The proof tree:
///   outer_ax_mp
///   ├── hyp2 proof (UHyp 1 pops this): step D = ax_1(a, N) → |- imp(a, M)
///   ├── hyp1 proof (UHyp 2 pops this): step C = inner_ax_mp → |- imp(imp(a,M), imp(a,a))
///   │   ├── hyp2 proof: step A = ax_1(a, M) → |- imp(a, imp(M, a))
///   │   └── hyp1 proof: step B = ax_2(a, M, a) → |- big expression
///
/// ax_mp unify: conclusion, UHyp(hyp2=a), UHyp(hyp1=imp(a,b))
/// In UThm mode, UHyp pops proofs from main stack (top first).
///
/// Required stack order for ax_mp: [..., |- hyp1_proof, |- hyp2_proof, arg1, arg2, concl]
///   UHyp 1 pops |- hyp2_proof (top after args popped) — must be proof of arg1
///   UHyp 2 pops |- hyp1_proof — must be proof of imp(arg1, arg2)
///
/// So for inner ax_mp: stack must be [|- B (hyp1), |- A (hyp2/top)]
///   → Do step B first, then step A
///
/// For outer ax_mp: stack must be [|- C (hyp1), |- D (hyp2/top)]
///   → Do inner ax_mp (gives |- C) first, then step D
fn write_proof_id(p: &mut impl Write) -> io::Result<()> {
    // Heap starts: [a] (index 0)
    //
    // We'll build expressions and save to heap as we go.
    // After building each expression, TermSave leaves it on both stack and heap.
    // We need to plan so that the stack layout matches what Thm expects.
    //
    // Strategy: Build everything the outer ax_mp needs, from bottom to top.
    //
    // The outer ax_mp needs (bottom to top):
    //   |- step_D_result     (hyp2 of outer ax_mp)
    //   |- step_C_result     (hyp1 of outer ax_mp)
    //   arg_a = imp(a, M)
    //   arg_b = imp(a, a)
    //   conclusion = imp(a, a)
    //
    // But step_C_result itself comes from an inner ax_mp which needs its own stack layout.
    // And step_D comes from ax_1 which also needs stack layout.
    //
    // The key insight: we build the proof tree bottom-up (leaves first), and each
    // Thm application consumes its inputs and pushes |- result.
    //
    // So the sequence is:
    // 1. Do step A (ax_1) → pushes |- A_result
    // 2. Do step B (ax_2) → pushes |- B_result
    // 3. Do step C (ax_mp) consuming A and B → pushes |- C_result
    // 4. Do step D (ax_1) → pushes |- D_result
    //    But wait — C_result and D_result are the hyps for the outer ax_mp,
    //    and they need to be in the right order on the stack.
    //
    // For the outer ax_mp, during unification:
    //   UHyp pops |- hyp1 first, then |- hyp2.
    //   hyp1 = imp(a', b') where a' = imp(a,M) and b' = imp(a,a)
    //   hyp1 = step_C_result = imp(imp(a,M), imp(a,a))
    //   hyp2 = a' = imp(a, M) = step_D_result
    //
    // Stack layout before outer Thm ax_mp:
    //   [..., |- D_result, |- C_result, arg1, arg2, conclusion]
    //
    // So D_result should be BELOW C_result. That means we do:
    //   step D first, then step C (or we reorder).
    //
    // Actually wait. During unification, UHyp pops from the main stack.
    // After Thm pops e, en, ..., e1, the main stack is [...].
    // Then UHyp 1 pops the top of [...], which is the most recently pushed item.
    //
    // If the stack before Thm is:
    //   [|- D, |- C, arg1, arg2, e]
    // Then Thm pops e, arg2, arg1 → main stack = [|- D, |- C]
    // UHyp 1 pops |- C (top)
    // UHyp 2 pops |- D
    //
    // So hyp1 (from first UHyp) = C_result, hyp2 (from second UHyp) = D_result.
    // And ax_mp's unify says: hyp1 = imp(a, b), hyp2 = a.
    // So C_result = imp(a', b') and D_result = a'.
    //
    // C_result = imp(imp(a,M), imp(a,a)) → a' = imp(a,M), b' = imp(a,a) ✓
    // D_result = imp(a, M) = a' ✓
    //
    // So the order is: push D, push C, push args, push conclusion, Thm ax_mp.
    // Meaning: do step D first (it ends up deeper), then step C (on top).
    //
    // But step C itself needs inputs from A and B. Let's think about
    // what the stack looks like at each point.
    //
    // Full sequence:
    //
    // 1. Build helper expressions (not(a), M=imp(not(a),a)) and save to heap
    //    These are just expressions, not proofs.
    //    But TermSave leaves them on the stack — I need to deal with that.
    //    Solution: don't use TermSave for these; build them with Term and
    //    use Save manually only when I want them on the heap.
    //    Actually, TermSave = Term + Save, and Save pushes back to stack.
    //    So TermSave always leaves the term on the stack.
    //
    //    Hmm, I could use TermSave and then later, these values get consumed
    //    by a Thm application. But the stack ordering has to be precise.
    //
    // Let me try a more direct approach. I'll build everything in-place.
    //
    // Let me think about what goes on the stack for each Thm call.
    //
    // ══ Step D: ax_1(a, not(a)) → |- imp(a, imp(not(a), a)) ══
    //
    // ax_1 has 2 args, 0 hyps.
    // Stack before Thm ax_1: [arg1=a, arg2=not(a), concl=imp(a, imp(not(a), a))]
    //
    // Commands:
    //   Ref 0                          → [a]
    //   Ref 0, Term not                → [a, not(a)]
    //   Save                           → [a, not(a)]   heap[1] = not(a)
    //
    // Wait, Save pops and pushes: "Pop any stack element s, push s to heap and stack."
    // So Save leaves it on the stack too. Stack = [a, not(a)], heap[1] = not(a).
    //
    //   Ref 0                          → [a, not(a), a]
    //   Ref 1                          → [a, not(a), a, not(a)]
    //   Ref 0                          → [a, not(a), a, not(a), a]
    //   Term imp                       → [a, not(a), a, imp(not(a), a)]
    //   Save                           → [a, not(a), a, imp(not(a), a)]  heap[2]=M
    //   Term imp                       → [a, not(a), imp(a, imp(not(a), a))]
    //   ThmSave ax_1                   → [|- imp(a, M)]  heap[3] = |- imp(a, M)
    //
    // Wait, Thm ax_1 pops: conclusion=imp(a,M), then arg2=not(a), then arg1=a.
    // Stack after: [|- imp(a, M)].
    // ThmSave also saves to heap. heap[3] = |- imp(a, M).
    //
    // Actually wait. The stack also has stuff below from the build steps.
    // Let me re-trace more carefully.
    //
    // Start: stack = [], heap = [a (idx 0)]
    //
    // Ref 0        → stack: [a]
    // Ref 0        → stack: [a, a]
    // Term not     → stack: [a, not(a)]      (pops a, pushes not(a))
    // Save         → stack: [a, not(a)]      heap: [a, not(a)(idx 1)]
    //                (Save pops not(a), pushes to heap, pushes back to stack)
    //
    // Now build conclusion: imp(a, imp(not(a), a))
    // First build imp(not(a), a):
    // Ref 1        → stack: [a, not(a), not(a)]
    // Ref 0        → stack: [a, not(a), not(a), a]
    // Term imp     → stack: [a, not(a), imp(not(a), a)]  (pops not(a) and a)
    // Save         → stack: [a, not(a), imp(not(a), a)]  heap: [a, not(a), M(idx 2)]
    //
    // Now build imp(a, M):
    // Ref 0        → stack: [a, not(a), M, a]
    // Ref 2        → stack: [a, not(a), M, a, M]
    // Term imp     → stack: [a, not(a), M, imp(a, M)]
    //
    // Now apply Thm ax_1:
    // Stack needs to be: [..., arg1=a, arg2=not(a), conclusion=imp(a,M)]
    // Current stack: [a, not(a), M, imp(a, M)]
    //
    // The M is in the way! It'll be consumed as arg2 or arg1...
    //
    // Thm ax_1 pops: conclusion=imp(a,M), arg2=M, arg1=not(a)
    // But arg1 should be a, arg2 should be not(a)!
    // And the uheap becomes [not(a), M], which doesn't match the unify stream.
    //
    // The unify stream for ax_1 is: UTerm(imp), URef(0), UTerm(imp), URef(1), URef(0)
    // This encodes imp(a, imp(b, a)) where a=uheap[0] and b=uheap[1].
    // With uheap = [not(a), M]:
    //   UTerm(imp): pop imp(a, M), check head=imp, push a and M
    //   URef(0): pop, check = uheap[0] = not(a) → FAIL because we get a, not not(a)
    //
    // So the stack ordering is wrong. I need to be much more careful about
    // what's on the stack and in what order.
    //
    // KEY REALIZATION: I can't leave intermediate expressions on the stack
    // willy-nilly. Each expression I build stays on the stack unless consumed
    // by a Thm. I should only build expressions that will immediately be
    // consumed as args/conclusion of a Thm, or carefully manage the stack.
    //
    // Alternative: Build helper expressions, save to heap, but DON'T leave
    // them on the stack. But there's no way to pop without consuming...
    // unless a Thm consumes them.
    //
    // BETTER APPROACH: Use Ref to push things from the heap right before
    // they're needed by a Thm. Only save to heap what I'll need later.
    // Don't build things on the stack that aren't immediately consumed.
    //
    // Let me think about this differently. The proof is a tree:
    //
    //   ax_mp
    //   ├── ax_mp
    //   │   ├── ax_2  (no hyps, 3 args)
    //   │   └── ax_1  (no hyps, 2 args)
    //   └── ax_1      (no hyps, 2 args)
    //
    // In reverse polish notation (postfix), the tree traversal is:
    //
    //   [build step D args+concl] Thm ax_1
    //   [build inner ax_1 args+concl] Thm ax_1
    //   [build inner ax_2 args+concl] Thm ax_2
    //   [build inner ax_mp args+concl] Thm ax_mp
    //   [build outer ax_mp args+concl] Thm ax_mp
    //
    // But the hyps for ax_mp come from the STACK, not from args.
    // The result of each sub-proof (|- ...) stays on the stack and is
    // consumed as a hypothesis by a later ax_mp.
    //
    // For the outer ax_mp, I need (bottom to top before Thm):
    //   |- D_result
    //   |- C_result
    //   outer_arg1 = imp(a, M)
    //   outer_arg2 = imp(a, a)
    //   outer_concl = imp(a, a)
    //
    // For step C (inner ax_mp), I need:
    //   |- A_result
    //   |- B_result
    //   inner_arg1 = ...
    //   inner_arg2 = ...
    //   inner_concl = ...
    //
    // But step C's result goes onto the stack as |- C_result.
    // And step D's result also goes onto the stack as |- D_result.
    // D must be below C on the stack.
    //
    // So the order is:
    //   1. Do step D → |- D on stack
    //   2. Do step A → |- A on stack (for inner ax_mp)
    //   3. Do step B → |- B on stack (for inner ax_mp)
    //      Now stack: [|- D, |- A, |- B]
    //   4. Push inner ax_mp args and concl, then Thm ax_mp → consumes |- B, |- A
    //      Now stack: [|- D, |- C]
    //   5. Push outer ax_mp args and concl, then Thm ax_mp → consumes |- C, |- D
    //      Now stack: [|- id]
    //
    // Wait, step 4: inner ax_mp has hyps. The first UHyp pops the top hypothesis,
    // which is |- B (on top). The second UHyp pops |- A.
    // Then ax_mp unifies: hyp1 = B_result = imp(inner_a, inner_b),
    //                     hyp2 = A_result = inner_a.
    // B_result should be the implication, A_result should match inner_a.
    //
    // Hmm wait. For the inner ax_mp:
    //   hyp1 (first UHyp pops) should be imp(inner_a, inner_b)
    //   hyp2 (second UHyp pops) should be inner_a
    //
    // The first UHyp pops the TOP of the main stack after args are popped.
    // So the hyps are: hyp1 = topmost, hyp2 = second.
    //
    // If the stack before inner Thm ax_mp is:
    //   [|- D, |- A, |- B, inner_arg1, inner_arg2, inner_concl]
    //
    // Thm pops: inner_concl, inner_arg2, inner_arg1
    // Remaining stack: [|- D, |- A, |- B]
    // UHyp 1 pops: |- B (top)
    // UHyp 2 pops: |- A
    //
    // So hyp1 = B_result, hyp2 = A_result.
    // In ax_mp's unify: hyp1 = imp(a_mp, b_mp), hyp2 = a_mp.
    // So B_result = imp(a_mp, b_mp) and A_result = a_mp.
    //
    // B_result = ax_2 result = imp(imp(a,imp(M,a)), imp(imp(a,M), imp(a,a)))
    // This has form imp(X, Y) where X = imp(a, imp(M, a)), Y = imp(imp(a,M), imp(a,a))
    // So a_mp = X = imp(a, imp(M, a))
    //    b_mp = Y = imp(imp(a,M), imp(a,a))
    //
    // A_result = ax_1 result = imp(a, imp(M, a)) = X = a_mp ✓
    //
    // The inner_arg1 (first arg to ax_mp, called 'a' in ax_mp's signature) = a_mp = X
    // The inner_arg2 (second arg, called 'b' in ax_mp's signature) = b_mp = Y
    // The inner_concl = b_mp = Y (conclusion = b in ax_mp)
    //
    // Great. So the inner Thm ax_mp is: inner_arg1 = X, inner_arg2 = Y, inner_concl = Y.
    //
    // After inner ax_mp: stack = [|- D, |- C_result]
    // C_result = b_mp = Y = imp(imp(a,M), imp(a,a))
    //
    // For outer ax_mp:
    // Stack before: [|- D, |- C, outer_arg1, outer_arg2, outer_concl]
    // Thm pops: outer_concl, outer_arg2, outer_arg1
    // Remaining: [|- D, |- C]
    // UHyp 1 pops: |- C (hyp1 = imp(outer_a, outer_b))
    // UHyp 2 pops: |- D (hyp2 = outer_a)
    //
    // C_result = imp(imp(a,M), imp(a,a)) = imp(outer_a, outer_b)
    // → outer_a = imp(a, M), outer_b = imp(a, a)
    // D_result = imp(a, M) = outer_a ✓
    //
    // outer_arg1 = outer_a = imp(a, M)
    // outer_arg2 = outer_b = imp(a, a)
    // outer_concl = outer_b = imp(a, a)
    //
    // After outer ax_mp: stack = [|- imp(a, a)] ✓
    //
    // Now let me figure out the exact proof commands.
    //
    // START: heap = [a(0)], stack = []
    //
    // ── Build not(a) and M=imp(not(a),a) in heap only ──
    // I need not(a) and M in the heap for later reference, but I don't want
    // them cluttering the stack. Problem: I can't build without putting on stack.
    //
    // Solution: build them, save to heap, then they'll sit on the stack.
    // But then the first Thm call needs to not consume them as args!
    //
    // Hmm, this is tricky. The issue is that building an expression always
    // pushes it onto the stack, and there's no "pop" instruction.
    //
    // What if I build not(a) and M as part of step D's argument building?
    //
    // Step D: ax_1(a, not(a))
    // Stack before Thm ax_1: [arg1=a, arg2=not(a), concl=imp(a, imp(not(a), a))]
    //
    // Commands:
    //   Ref(0)            → [a]              ← arg1
    //   Ref(0)            → [a, a]
    //   TermSave(not)     → [a, not(a)]      ← arg2, heap[1] = not(a)
    //   Ref(0)            → [a, not(a), a]
    //   Ref(1)            → [a, not(a), a, not(a)]
    //   Ref(0)            → [a, not(a), a, not(a), a]
    //   TermSave(imp)     → [a, not(a), a, imp(not(a),a)]  heap[2] = M
    //   Term(imp)         → [a, not(a), imp(a, M)]         ← concl
    //   ThmSave(ax_1)     → [|- imp(a, M)]   heap[3] = |- D_result
    //
    // Wait, after TermSave(imp) for M, stack = [a, not(a), a, M].
    // No wait. TermSave(imp) pops 2 args (not(a) and a), pushes M.
    // Before: [a, not(a), a, not(a), a]
    // TermSave(imp): pops a (top) and not(a), pushes imp(not(a), a) = M, saves.
    // After: [a, not(a), a, M]
    //
    // Then Term(imp): pops M and a, pushes imp(a, M).
    // After: [a, not(a), imp(a, M)]
    //
    // Then ThmSave(ax_1):
    //   Pop concl = imp(a, M)
    //   Pop arg2 = not(a)
    //   Pop arg1 = a
    //   uheap = [a, not(a)]
    //   Unify imp(a, M) against imp(uheap[0], imp(uheap[1], uheap[0]))
    //       = imp(a, imp(not(a), a)) = imp(a, M) ✓
    //   Push |- imp(a, M), save to heap
    // After: stack = [|- imp(a, M)], heap = [a, not(a), M, |- D_result]
    //
    // Wait, the heap indices:
    // idx 0: a
    // idx 1: not(a)  [from TermSave(not)]
    // idx 2: M = imp(not(a), a)  [from TermSave(imp)]
    // idx 3: |- imp(a, M)  [from ThmSave(ax_1)]
    //
    // But wait, ThmSave means Thm + Save. Save takes the result (|- imp(a,M))
    // and saves to heap. So heap[3] = |- imp(a, M). ✓
    //
    // Stack: [|- D_result]
    //
    // ── Step A: ax_1(a, M) → |- imp(a, imp(M, a)) ──
    //
    // Need: [|- D, arg1=a, arg2=M, concl=imp(a, imp(M, a))]
    //
    //   Ref(0)            → [|- D, a]                ← arg1
    //   Ref(2)            → [|- D, a, M]             ← arg2
    //   Ref(0)            → [|- D, a, M, a]
    //   Ref(2)            → [|- D, a, M, a, M]
    //   Ref(0)            → [|- D, a, M, a, M, a]
    //   Term(imp)         → [|- D, a, M, a, imp(M, a)]
    //   Term(imp)         → [|- D, a, M, imp(a, imp(M, a))]  ← concl
    //   Thm(ax_1)         → [|- D, |- imp(a, imp(M, a))]
    //
    // Thm ax_1 pops: concl=imp(a, imp(M,a)), arg2=M, arg1=a
    // uheap = [a, M]
    // Unify: imp(a, imp(M, a)) vs imp(uheap[0], imp(uheap[1], uheap[0]))
    //   = imp(a, imp(M, a)) ✓
    // Push |- imp(a, imp(M, a))
    //
    // Stack: [|- D, |- A_result]
    //
    // ── Step B: ax_2(a, M, a) ──
    // ax_2 has 3 args, 0 hyps
    // conclusion = imp(imp(a, imp(M, a)), imp(imp(a, M), imp(a, a)))
    //
    // I need to build this big expression. Let me use heap refs to build it.
    // The conclusion is: imp(imp(a, imp(M, a)), imp(imp(a, M), imp(a, a)))
    //
    // Let me decompose:
    //   LHS = imp(a, imp(M, a))  ← we just proved this as A_result!
    //         But it's the expression, not the proof. We need to build the expression.
    //   RHS = imp(imp(a, M), imp(a, a))
    //     imp(a, M) ← this is D_result's expression content!
    //     imp(a, a) ← this is what we want to prove
    //
    // Need: [|- D, |- A, arg1=a, arg2=M, arg3=a, concl=imp(LHS, RHS)]
    //
    // I have a, M, not(a) in the heap. Let me build:
    //
    //   Ref(0)      → [|- D, |- A, a]
    //   Ref(2)      → [|- D, |- A, a, M]
    //   Ref(0)      → [|- D, |- A, a, M, a]
    //   -- Now build the conclusion
    //   -- imp(imp(a, imp(M, a)), imp(imp(a, M), imp(a, a)))
    //   -- inner1 = imp(a, imp(M, a)):
    //   Ref(0)      → [..., a]
    //   Ref(2)      → [..., a, M]
    //   Ref(0)      → [..., a, M, a]
    //   Term(imp)   → [..., a, imp(M, a)]
    //   Term(imp)   → [..., imp(a, imp(M, a))]
    //
    // Hmm this is getting really long. Let me see if I can use Save to cache intermediate results.
    //
    // Actually, at this point the full stack is:
    //   [|- D, |- A, a, M, a, imp(a, imp(M, a))]
    //
    //   -- inner2 = imp(a, M):
    //   Ref(0)      → [..., imp(a, imp(M, a)), a]
    //   Ref(2)      → [..., imp(a, imp(M, a)), a, M]
    //   Term(imp)   → [..., imp(a, imp(M, a)), imp(a, M)]
    //   -- inner3 = imp(a, a):
    //   Ref(0)      → [..., imp(a, M), a]
    //   Ref(0)      → [..., imp(a, M), a, a]
    //   Term(imp)   → [..., imp(a, M), imp(a, a)]
    //   -- imp(inner2, inner3):
    //   Term(imp)   → [..., imp(imp(a, M), imp(a, a))]
    //   -- imp(inner1, imp(inner2, inner3)):
    //   Term(imp)   → [..., conclusion]
    //
    // Let me trace the full stack at this point:
    // [|- D, |- A, a, M, a, conclusion]
    //
    //   Thm(ax_2)   → pops: conclusion, a(arg3), M(arg2), a(arg1)
    //                  uheap = [a, M, a]
    //                  Unifies conclusion against ax_2's expression.
    //                  pushes |- conclusion
    //
    // Stack: [|- D, |- A, |- B_result]
    //
    // ── Step C: ax_mp(inner) ──
    // Stack before: needs hyps and args below
    //
    // Currently stack: [|- D, |- A, |- B]
    // For Thm ax_mp, need: [..., |- hyp2, |- hyp1, arg1, arg2, concl]
    // where hyp1 (first UHyp) = B_result, hyp2 (second UHyp) = A_result
    //
    // So: [|- D, |- A(hyp2), |- B(hyp1), arg1, arg2, concl]
    // After Thm pops concl, arg2, arg1: stack = [|- D, |- A, |- B]
    // UHyp 1 pops |- B (top) = hyp1 ✓
    // UHyp 2 pops |- A = hyp2 ✓
    //
    // Need to push: arg1, arg2, concl for the inner ax_mp.
    // inner ax_mp's (a, b) args are:
    //   a_mp = imp(a, imp(M, a)) (= A_result expression)
    //   b_mp = imp(imp(a, M), imp(a, a)) (= B_result's second half)
    //
    // concl = b_mp = imp(imp(a, M), imp(a, a))
    //
    // Build arg1 = imp(a, imp(M, a)):
    //   Ref(0), Ref(2), Ref(0), Term(imp), Term(imp)
    //
    // Build arg2 = concl = imp(imp(a, M), imp(a, a)):
    //   Ref(0), Ref(2), Term(imp), Ref(0), Ref(0), Term(imp), Term(imp)
    //
    // And we need concl again. But concl = arg2, so we could use Save and Ref.
    //
    // Let me use TermSave for the conclusion:
    //
    //   -- arg1 = imp(a, imp(M, a)):
    //   Ref(0)      → [|- D, |- A, |- B, a]
    //   Ref(2)      → [|- D, |- A, |- B, a, M]
    //   Ref(0)      → [|- D, |- A, |- B, a, M, a]
    //   Term(imp)   → [|- D, |- A, |- B, a, imp(M, a)]
    //   Term(imp)   → [|- D, |- A, |- B, imp(a, imp(M, a))]  ← arg1
    //
    //   -- arg2 = imp(imp(a,M), imp(a,a)):
    //   Ref(0)      → [..., a]
    //   Ref(2)      → [..., a, M]
    //   Term(imp)   → [..., imp(a, M)]
    //   Ref(0)      → [..., imp(a, M), a]
    //   Ref(0)      → [..., imp(a, M), a, a]
    //   Term(imp)   → [..., imp(a, M), imp(a, a)]
    //   TermSave(imp) → [..., imp(imp(a,M), imp(a,a))]  heap[4] = this
    //
    // Hmm wait, this TermSave creates arg2 and saves to heap. But I also need
    // the same expression as concl.
    //
    //   Ref(4)      → [..., imp(imp(a,M), imp(a,a)), imp(imp(a,M), imp(a,a))]
    //
    // Wait, but the heap index might not be 4. Let me count heap slots.
    //
    // heap after step D: [a(0), not(a)(1), M(2), |- D(3)]
    // Step A doesn't save anything new (used Thm not ThmSave)
    // Step B doesn't save anything new
    //
    // So next TermSave would be heap[4]. But wait — the proof builder tracks
    // its own heap, and in the proof stream, the heap is initialized with the
    // theorem's args. The theorem `id` has 1 arg (a), so:
    //   heap[0] = a
    //   heap[1] = next save = not(a) from step D's TermSave(not)
    //   heap[2] = M from step D's TermSave(imp)
    //   heap[3] = |- D_result from step D's ThmSave(ax_1)
    //
    // Step A uses Thm (not ThmSave), so no new heap entry.
    // Step B uses Thm, no new heap entry.
    //
    // Next save would be heap[4].
    //
    // OK so:
    //   TermSave(imp) → heap[4] = inner_arg2/concl = imp(imp(a,M), imp(a,a))
    //   Ref(4)        → pushes copy of heap[4] for concl
    //
    // But Ref(4) won't work here because we need distinct objects!
    // The spec says equality is POINTER equality, not structural.
    // Ref(4) gives back the SAME pointer, so Refl will work.
    //
    // Actually wait, we need arg2 and concl to be the same pointer for
    // ax_mp's unification to work (conclusion must equal b).
    //
    // So: after TermSave, stack has the expression. Then Ref(4) pushes
    // the same pointer again.
    //
    //   -- concl (same as arg2):
    //   Ref(4)      → [..., arg2, concl]   (both point to same expression)
    //
    // Full stack before Thm ax_mp:
    //   [|- D, |- A, |- B, arg1, arg2, concl]
    //
    //   Thm(ax_mp)  → pops concl, arg2, arg1; uheap = [arg1, arg2]
    //                  UHyp 1 pops |- B (hyp1)
    //                  UHyp 2 pops |- A (hyp2)
    //                  Unifies...
    //                  pushes |- concl = |- imp(imp(a,M), imp(a,a))
    //
    // Wait — ax_mp's unify says conclusion = uheap[1] = arg2 = concl.
    // And we set concl = arg2 (same pointer). ✓
    //
    // After inner ax_mp: stack = [|- D, |- C_result]
    // Save |- C_result to heap? We'll see if we need it.
    //
    // ── Step E: outer ax_mp ──
    // Stack: [|- D, |- C]
    // Need: [|- D(hyp2), |- C(hyp1), arg1, arg2, concl]
    //
    // outer arg1 = imp(a, M) = Ref(0), Ref(2), Term(imp)
    //   But wait, we need the SAME pointer as in D_result's content!
    //   If D_result = |- imp(a, M), then during unification UHyp 2 will
    //   pop |- D and push D's expression to the unify stack. That expression
    //   is the imp(a, M) that was built during step D.
    //
    //   But arg1 for the outer ax_mp's main args doesn't need to be the same
    //   pointer — the arg1 in the main stack is used to initialize uheap[0],
    //   and then URef(0) checks that hyp2's expression matches uheap[0].
    //   But the check IS pointer equality!
    //
    //   Hmm, so I need arg1 to be the SAME pointer as D_result's expression.
    //   But D_result was built in step D and I didn't save the expression
    //   separately — I only saved |- D_result.
    //
    //   Wait, actually |- D_result contains the expression imp(a, M). When
    //   UHyp pops |- D_result, it pushes the expression onto the unify stack.
    //   Then URef(0) checks that this expression equals uheap[0].
    //
    //   uheap[0] = arg1 (the first arg we supply to the outer ax_mp).
    //   If arg1 was built fresh with Ref(0), Ref(2), Term(imp), it's a
    //   NEW imp(a, M) expression — a different pointer!
    //
    //   So the check `URef(0)` would fail because the D_result's imp(a,M)
    //   is a different object from the freshly built imp(a,M).
    //
    //   This means I need to SAVE the imp(a, M) expression during step D
    //   and reuse it as arg1 of the outer ax_mp.
    //
    //   During step D, I built imp(a, M) as the conclusion of Thm ax_1.
    //   But Thm ax_1 doesn't return the expression — it returns |- expression.
    //   The expression is constructed internally.
    //
    //   Hmm, actually... let me re-read the spec:
    //
    //   "Term t: H; S, e1, ..., en --> H; S, (t e1 ... en)"
    //   "allocate (t e1 ... en)"
    //
    //   So each Term allocates a NEW expression. Two Term calls with the same
    //   sub-expressions produce DIFFERENT pointers.
    //
    //   "Ref i: H; S --> H; S, H[i]"
    //   Ref pushes the SAME pointer from the heap.
    //
    //   So to get the same pointer, I must use Save/TermSave and then Ref.
    //
    //   This means during step D, when I build the conclusion imp(a, M),
    //   I need to Save it to the heap so I can Ref it later. But the
    //   conclusion is consumed by Thm ax_1 and not saved separately.
    //
    //   Actually, looking at ThmSave:
    //   "ThmSave T = Thm T, Save"
    //   This saves the RESULT (|- e) to the heap, not the sub-expressions.
    //
    //   So heap[3] = |- imp(a, M). I can't get back just imp(a, M) from this.
    //   I'd need to have separately saved imp(a, M) before the Thm call.
    //
    //   Let me redesign step D to save imp(a, M) to the heap.
    //
    //   In step D, I build imp(a, M) as the conclusion. If I use TermSave
    //   for the final imp, it goes to the heap AND stays on the stack:
    //
    //   TermSave(imp) for imp(a, M) → heap[?], stack: [..., imp(a, M)]
    //   Then Thm(ax_1) uses it as the conclusion.
    //   But Thm pops the conclusion — it's gone from the stack.
    //   But it's still in the heap!
    //
    //   Wait, the conclusion expression imp(a, M) was saved to the heap via TermSave.
    //   Then Thm pops it from the stack to use as the conclusion for unification.
    //   After Thm, the expression is still in the heap.
    //   I can use Ref(heap_idx) to get it back later.
    //
    //   But will the unification inside Thm check pointer equality against this
    //   exact pointer? Yes! The conclusion is the same pointer that went into
    //   the heap (TermSave saves before popping from stack? Actually TermSave = Term + Save,
    //   and Save = pop, push to heap, push back to stack. So the pointer on the stack
    //   and in the heap are the same.)
    //
    //   So later, when I Ref that heap index, I get the same pointer back.
    //
    //   Now during the outer ax_mp, I supply this same pointer as arg1.
    //   Then ax_mp's unification does UHyp, pops |- D_result, pushes D's expression.
    //   D's expression (imp(a, M)) was the conclusion passed to step D's ax_1.
    //   This is the SAME pointer that I saved to the heap!
    //
    //   Wait... is it? When Thm ax_1 processes:
    //     Pop concl → the concl expression
    //     Pop args → the arg expressions
    //     Runs unification → verifies the args match the expression
    //     Pushes |- concl → |- concl uses the SAME concl pointer
    //
    //   So the expression inside |- D_result is the SAME pointer as what I
    //   saved to the heap. So Ref(heap_idx) gives me the same pointer, and
    //   pointer equality will hold. ✓
    //
    //   Great! Let me now plan the full proof with correct heap management.

    // FINAL PLAN:
    //
    // Heap: [a(0)]
    //
    // ── Step D: ax_1(a, not(a)) → |- imp(a, M) ──
    //   Ref(0)                 → [a]
    //   Ref(0)                 → [a, a]
    //   TermSave(not)          → [a, not(a)]         heap[1] = not(a)
    //   Ref(1)                 → [a, not(a), not(a)]
    //   Ref(0)                 → [a, not(a), not(a), a]
    //   TermSave(imp)          → [a, not(a), M]      heap[2] = M = imp(not(a), a)
    //   Ref(0)                 → [a, not(a), M, a]
    //   Ref(2)                 → [a, not(a), M, a, M]
    //   TermSave(imp)          → [a, not(a), M, imp(a,M)]  heap[3] = imp(a,M)
    //   -- Now: arg1=a, arg2=not(a), concl=M is wrong! Let me re-check.
    //   -- Thm ax_1 pops: concl=imp(a,M), arg2=M, arg1=not(a)
    //   -- But arg1 should be a! The stray M is in the way!
    //
    // The issue is that saving M to the heap also leaves it on the stack.
    // TermSave = Term + Save, and Save pushes back to stack.
    //
    // I need M in the heap but not on the stack. But there's no way to pop!
    //
    // Hmm. The only way to consume something from the stack is via Term (as args)
    // or Thm (as args/hyps). There's no discard operation.
    //
    // SOLUTION: Don't build M as a standalone expression. Instead, build it
    // in-place as part of the conclusion, and use Save/TermSave strategically.
    //
    // Actually, the cleaner solution: rearrange what's on the stack.
    //
    // For step D's Thm ax_1:
    //   Need: [arg1=a, arg2=not(a), concl=imp(a, imp(not(a), a))]
    //
    // I'll build concl using TermSave to save sub-expressions to the heap:
    //
    //   Ref(0)                 → [a]                              ← arg1
    //   Ref(0)                 → [a, a]
    //   TermSave(not)          → [a, not(a)]                      ← arg2, heap[1]=not(a)
    //   Ref(0)                 → [a, not(a), a]
    //   Ref(1)                 → [a, not(a), a, not(a)]
    //   Ref(0)                 → [a, not(a), a, not(a), a]
    //   TermSave(imp)          → [a, not(a), a, imp(not(a),a)]    heap[2]=M
    //   TermSave(imp)          → [a, not(a), imp(a, M)]           heap[3]=imp(a,M)
    //                             ← concl
    //   ThmSave(ax_1)          → [|- imp(a, M)]                   heap[4]=|- D_result
    //
    // Let me verify the Thm ax_1 pops:
    //   Pop concl = imp(a, M) [from top]
    //   Pop arg2 = not(a) [the not(a) at position 2]
    //   Pop arg1 = a [position 1]
    //   uheap = [a, not(a)]
    //   Unify concl against imp(uheap[0], imp(uheap[1], uheap[0]))
    //     = imp(a, imp(not(a), a)) = imp(a, M) ✓
    //   Push |- imp(a, M), ThmSave saves to heap[4]
    //
    // Heap: [a(0), not(a)(1), M(2), imp(a,M)(3), |- D(4)]
    // Stack: [|- D]
    //
    // ── Step A: ax_1(a, M) → |- imp(a, imp(M, a)) ──
    //   Ref(0)                 → [|- D, a]                        ← arg1
    //   Ref(2)                 → [|- D, a, M]                     ← arg2
    //   Ref(0)                 → [|- D, a, M, a]
    //   Ref(2)                 → [|- D, a, M, a, M]
    //   Ref(0)                 → [|- D, a, M, a, M, a]
    //   Term(imp)              → [|- D, a, M, a, imp(M, a)]
    //   TermSave(imp)          → [|- D, a, M, imp(a, imp(M,a))]  heap[5]=imp(a,imp(M,a))
    //                             ← concl
    //   Thm(ax_1)              → [|- D, |- A]
    //
    // Thm ax_1 pops: concl=imp(a,imp(M,a)), arg2=M, arg1=a
    // uheap = [a, M]
    // Unify: imp(a, imp(M, a)) vs imp(uheap[0], imp(uheap[1], uheap[0]))
    //   = imp(a, imp(M, a)) ✓
    // Push |- imp(a, imp(M, a))
    //
    // Heap: [a(0), not(a)(1), M(2), imp(a,M)(3), |-D(4), imp(a,imp(M,a))(5)]
    // Stack: [|- D, |- A]
    //
    // ── Step B: ax_2(a, M, a) ──
    // Conclusion: imp(imp(a,imp(M,a)), imp(imp(a,M), imp(a,a)))
    //
    //   Ref(0)                 → [|- D, |- A, a]                  ← arg1
    //   Ref(2)                 → [|- D, |- A, a, M]               ← arg2
    //   Ref(0)                 → [|- D, |- A, a, M, a]            ← arg3
    //
    //   -- Build conclusion:
    //   -- imp(imp(a,imp(M,a)), imp(imp(a,M), imp(a,a)))
    //   -- Part 1: imp(a, imp(M, a)) — same pointer as heap[5]!
    //   Ref(5)                 → [..., a, imp(a, imp(M,a))]
    //
    //   -- Part 2: imp(imp(a,M), imp(a,a))
    //   -- imp(a, M) = heap[3]
    //   Ref(3)                 → [..., imp(a,imp(M,a)), imp(a,M)]
    //   -- imp(a, a) — build fresh:
    //   Ref(0)                 → [..., imp(a,M), a]
    //   Ref(0)                 → [..., imp(a,M), a, a]
    //   TermSave(imp)          → [..., imp(a,M), imp(a,a)]   heap[6]=imp(a,a)
    //   Term(imp)              → [..., imp(imp(a,M), imp(a,a))]
    //
    //   -- Outer: imp(part1, part2)
    //   Term(imp)              → [..., imp(imp(a,imp(M,a)), imp(imp(a,M),imp(a,a)))]
    //                             ← concl
    //
    // Full stack: [|- D, |- A, a, M, a, concl]
    //   Thm(ax_2)  → pops: concl, a(arg3), M(arg2), a(arg1)
    //                 uheap = [a, M, a]
    //                 Unify concl against ax_2's expression...
    //                 Push |- concl
    // Stack: [|- D, |- A, |- B]
    //
    // But wait — in the ax_2 unification, we need pointer equality checks.
    // The unify stream for ax_2 references URef(0)=a, URef(1)=M, URef(2)=a.
    //
    // The conclusion we built uses Ref(5) for imp(a,imp(M,a)). Inside this
    // expression, the 'a' is heap[0] (the original a variable), and M is heap[2].
    // So when unification decomposes, it should find the same pointers.
    //
    // Let me trace the ax_2 unification:
    // uheap = [a(arg1), M(arg2), a(arg3)]
    // Note: arg1 and arg3 are both Ref(0) = the SAME pointer. ✓
    // unify_stack = [concl]
    //
    // UTerm(imp): pop concl = imp(imp(a,imp(M,a)), imp(imp(a,M),imp(a,a)))
    //   Check head=imp ✓. Push arg2=imp(imp(a,M),imp(a,a)), arg1=imp(a,imp(M,a)).
    //   (Wait — "push en, ..., e1" — for imp(A, B), pushes B then A)
    //   After: unify_stack = [imp(a,imp(M,a)), imp(imp(a,M),imp(a,a))]
    //
    // UTerm(imp): pop imp(a,imp(M,a)). Check head=imp ✓. Push imp(M,a), a.
    //   After: unify_stack = [a, imp(M,a), imp(imp(a,M),imp(a,a))]
    //
    // URef(0): pop a. Check = uheap[0] = a ✓ (same pointer from Ref(0))
    //   After: unify_stack = [imp(M,a), imp(imp(a,M),imp(a,a))]
    //
    // UTerm(imp): pop imp(M,a). Check head=imp ✓. Push a, M.
    //   After: unify_stack = [M, a, imp(imp(a,M),imp(a,a))]
    //
    // URef(1): pop M. Check = uheap[1] = M ✓ (Ref(2) in the proof gives heap[2] = M)
    //   Wait — uheap[1] is the second arg to Thm, which is Ref(2) = heap[2] = M.
    //   And the M inside imp(M,a) was built using Ref(2) in step A (when we built
    //   imp(a, imp(M, a)) = heap[5]). Actually no — in step B, we used Ref(5) to
    //   get imp(a, imp(M, a)) from the heap. That expression was built in step A
    //   using Ref(2) for M. So the M pointer inside is the same as heap[2].
    //   And uheap[1] = arg2 = Ref(2) = heap[2] = same M pointer.
    //   So URef(1) check passes. ✓
    //
    // URef(2): pop a. Check = uheap[2] = a ✓ (arg3 = Ref(0) = heap[0] = a, same pointer)
    //   After: unify_stack = [imp(imp(a,M),imp(a,a))]
    //
    // UTerm(imp): pop imp(imp(a,M),imp(a,a)). Check head=imp ✓.
    //   Push imp(a,a), imp(a,M).
    //   After: unify_stack = [imp(a,M), imp(a,a)]
    //
    // UTerm(imp): pop imp(a,M). Check head=imp ✓. Push M, a.
    //   After: unify_stack = [a, M, imp(a,a)]
    //
    // URef(0): pop a. Check = uheap[0] = a ✓
    // URef(1): pop M. Check = uheap[1] = M ✓
    //   After: unify_stack = [imp(a,a)]
    //
    // UTerm(imp): pop imp(a,a). Check head=imp ✓. Push a, a.
    //   After: unify_stack = [a, a]
    //
    // URef(0): pop a. Check = uheap[0] = a ✓
    // URef(2): pop a. Check = uheap[2] = a ✓
    //   After: unify_stack = []
    //
    // Unification done! ✓
    //
    // But wait — I need to double-check the pointer equality for imp(a,M) in part 2.
    // In the conclusion, imp(a,M) was built via Ref(3) = heap[3]. This is the same
    // imp(a,M) that was built in step D. The M inside it is the same heap[2] pointer.
    // The a inside it is the same heap[0] pointer. So when unification decomposes it,
    // the pointers match. ✓
    //
    // And imp(a,a) was built fresh in step B with TermSave giving heap[6].
    // The a's inside it are both Ref(0) = heap[0], same pointer. ✓
    //
    // OK, ax_2 unification passes.
    //
    // After step B: stack = [|- D, |- A, |- B]
    // Heap: [a(0), not(a)(1), M(2), imp(a,M)(3), |-D(4), imp(a,imp(M,a))(5), imp(a,a)(6)]
    //
    // ── Step C: inner ax_mp ──
    // Need: [|- D, |- A(hyp2), |- B(hyp1), inner_arg1, inner_arg2, inner_concl]
    //
    // inner_arg1 = imp(a, imp(M, a)) = heap[5]
    // inner_arg2 = inner_concl = imp(imp(a,M), imp(a,a))
    //
    // But I didn't save imp(imp(a,M), imp(a,a)) to the heap! It was consumed by
    // Thm ax_2 as the conclusion. And Thm returns |- concl, but the concl expression
    // itself is inside the |- and I can't extract it.
    //
    // I need to save it before Thm ax_2 consumes it. Let me use TermSave for the
    // final Term(imp) that builds the conclusion in step B.
    //
    // Actually wait. Let me look at the save more carefully. What Thm returns is
    // |- concl where concl is the expression we passed. The expression is saved
    // inside the |- proof object. But I need the expression separately.
    //
    // The conclusion expression was built as the top of the stack before Thm ax_2.
    // I should save it to the heap BEFORE calling Thm ax_2.
    //
    // But if I Save it, it stays on the stack too. Then Thm ax_2 will pop it as concl.
    // That's fine — it's still on the heap for later use.
    //
    // So in step B, I should TermSave the final conclusion, or Save after building it.
    //
    // Actually — looking at what I need for inner_arg2 and inner_concl:
    // inner_arg2 should be imp(imp(a,M), imp(a,a)). This is the CONCLUSION of ax_2.
    // But it's also what I want to prove (the conclusion of the inner ax_mp).
    // And I need it TWICE on the stack (once as arg2, once as concl for ax_mp).
    //
    // For ax_mp's unification, concl must equal uheap[1] = arg2 (pointer equality).
    // So I need the SAME pointer for both. I can Save + Ref to achieve this.
    //
    // Let me also reconsider: I need inner_arg2 and inner_concl to be the same pointer.
    //
    // inner_arg1 = imp(a, imp(M, a)) → heap[5], use Ref(5)
    // inner_arg2 = imp(imp(a,M), imp(a,a)) → need to build and save
    // inner_concl = same as inner_arg2 → Ref from heap
    //
    // Hmm, but I also need this expression as the conclusion for step B's ax_2.
    // Let me save it during step B using TermSave, then reuse it for step C.
    //
    // Modified step B: use TermSave for the outermost Term(imp) of the conclusion.
    //
    // Actually, I realize there might be an issue. The full conclusion of ax_2 is:
    //   imp(imp(a,imp(M,a)), imp(imp(a,M), imp(a,a)))
    //
    // But inner_arg2 is only the second half: imp(imp(a,M), imp(a,a)).
    // And inner_arg1 is the first half: imp(a, imp(M, a)).
    //
    // So I need to save the two PARTS, not the whole thing.
    //
    // Actually wait, inner_arg1 and inner_arg2 are the args to the inner ax_mp,
    // which are the 'a' and 'b' of ax_mp's signature.
    //
    // The inner ax_mp maps: a_mp → inner_arg1, b_mp → inner_arg2
    // hyp1 = imp(a_mp, b_mp) = B_result = imp(inner_arg1, inner_arg2)
    //         = imp(imp(a,imp(M,a)), imp(imp(a,M),imp(a,a)))
    //         = the conclusion of ax_2. ✓
    // hyp2 = a_mp = A_result = imp(a, imp(M, a)) = inner_arg1. ✓
    // concl = b_mp = inner_arg2 = imp(imp(a,M), imp(a,a)).
    //
    // So inner_arg2 = inner_concl needs to be the same pointer, and it's the
    // SECOND part of B_result. The B_result expression has this as a sub-expression.
    //
    // If I build B_result using Ref for inner_arg2's sub-expression...
    //
    // Actually, during ax_2 unification, the unifier doesn't care about specific
    // sub-expression pointers — it only cares that the overall structure matches.
    // The unifier checks uheap[0]=a, uheap[1]=M, uheap[2]=a against the expression.
    //
    // But for the inner ax_mp, I need inner_arg2 as a standalone expression that
    // I can push twice on the stack (as arg2 and concl). And the B_result (|- expr)
    // contains this expression as a sub-expression, but I can't access sub-expressions
    // from |- values.
    //
    // So I need to:
    // 1. Build imp(imp(a,M), imp(a,a)) = C (save to heap)
    // 2. Build the full ax_2 conclusion using C: imp(heap[5], C)
    // 3. Apply Thm ax_2 → |- that conclusion
    // 4. For inner ax_mp: use Ref(5) as inner_arg1, Ref(heap_C) as inner_arg2,
    //    Ref(heap_C) again as inner_concl
    //
    // Let me redo step B with this in mind.
    //
    // After step A: heap = [a(0), not(a)(1), M(2), imp(a,M)(3), |-D(4), imp(a,imp(M,a))(5)]
    // Stack: [|- D, |- A]
    //
    // Step B (revised):
    //   Ref(0)     → [|- D, |- A, a]                              ← arg1
    //   Ref(2)     → [|- D, |- A, a, M]                           ← arg2
    //   Ref(0)     → [|- D, |- A, a, M, a]                        ← arg3
    //
    //   -- Build inner_arg2 = imp(imp(a,M), imp(a,a)), save to heap
    //   Ref(3)     → [..., a, imp(a,M)]
    //   Ref(0)     → [..., imp(a,M), a]
    //   Ref(0)     → [..., imp(a,M), a, a]
    //   TermSave(imp) → [..., imp(a,M), imp(a,a)]                 heap[6]=imp(a,a)
    //   TermSave(imp) → [..., imp(imp(a,M), imp(a,a))]            heap[7]=C
    //
    //   -- Build full conclusion: imp(heap[5], heap[7])
    //   Ref(5)     → [..., C, imp(a,imp(M,a))]
    //   -- Hmm, order matters for Term(imp). imp takes (arg1, arg2) and
    //   -- builds imp(arg1, arg2). Stack must be: [..., arg1, arg2]
    //   -- where arg1 = imp(a,imp(M,a)) and arg2 = C.
    //   -- Currently stack top is: C, imp(a,imp(M,a))
    //   -- That gives imp(C, imp(a,imp(M,a))) which is wrong!
    //
    //   -- I need imp(imp(a,imp(M,a)), C) as the conclusion.
    //   -- So stack should be: imp(a,imp(M,a)), C
    //   -- But I pushed C first, then imp(a,imp(M,a)).
    //
    //   -- WAIT. Let me reconsider. Term pops args in the order they appear
    //   -- in the term declaration. For `term imp: wff > wff > wff`,
    //   -- Term imp pops e2 (top), e1 (below), pushes imp(e1, e2).
    //   -- So stack [..., e1, e2] → [..., imp(e1, e2)]
    //
    //   -- With C on stack first, then Ref(5) = imp(a,imp(M,a)):
    //   -- Stack: [..., C, imp(a,imp(M,a))]
    //   -- Term(imp) → imp(C, imp(a,imp(M,a))) ← wrong!
    //
    //   -- I need: [..., imp(a,imp(M,a)), C]
    //   -- So push Ref(5) BEFORE C:

    // Let me try yet another arrangement.
    //
    // Step B (revised again):
    //   Ref(0)     → [|- D, |- A, a]                              ← arg1
    //   Ref(2)     → [|- D, |- A, a, M]                           ← arg2
    //   Ref(0)     → [|- D, |- A, a, M, a]                        ← arg3
    //
    //   -- Build conclusion: imp(imp(a,imp(M,a)), imp(imp(a,M), imp(a,a)))
    //   -- First push the LHS: imp(a, imp(M, a)) = heap[5]
    //   Ref(5)     → [..., a, imp(a,imp(M,a))]
    //   -- Then build the RHS: imp(imp(a,M), imp(a,a))
    //   Ref(3)     → [..., imp(a,imp(M,a)), imp(a,M)]
    //   Ref(0)     → [..., imp(a,M), a]
    //   Ref(0)     → [..., imp(a,M), a, a]
    //   TermSave(imp) → [..., imp(a,M), imp(a,a)]                 heap[6]=imp(a,a)
    //   TermSave(imp) → [..., imp(imp(a,M), imp(a,a))]            heap[7]=C
    //   -- Now: [..., imp(a,imp(M,a)), C]
    //   Term(imp)  → [..., imp(imp(a,imp(M,a)), C)]               ← conclusion
    //
    // Full stack: [|- D, |- A, a, M, a, conclusion]
    //   Thm(ax_2) → pops conclusion, a, M, a
    //              → pushes |- B_result
    // Stack: [|- D, |- A, |- B]
    //
    // ── Step C: inner ax_mp ──
    //   Ref(5)     → [|- D, |- A, |- B, imp(a,imp(M,a))]          ← inner_arg1
    //   Ref(7)     → [|- D, |- A, |- B, imp(a,imp(M,a)), C]       ← inner_arg2
    //   Ref(7)     → [|- D, |- A, |- B, imp(a,imp(M,a)), C, C]    ← inner_concl (same ptr)
    //   Thm(ax_mp) → pops C(concl), C(arg2), imp(a,imp(M,a))(arg1)
    //                 uheap = [imp(a,imp(M,a)), C]
    //                 UHyp 1 pops |- B
    //                 UHyp 2 pops |- A
    //                 pushes |- C_result = |- C
    // Stack: [|- D, |- C]
    //
    // Let me verify inner ax_mp unification:
    // uheap = [imp(a,imp(M,a)), C]
    // where C = imp(imp(a,M), imp(a,a))
    //
    // Unify stream for ax_mp: UHyp, UTerm(imp), URef(0), URef(1), UHyp, URef(0), URef(1)
    //
    // unify_stack starts with: [C] (the conclusion we passed)
    //
    // UHyp: pop |- B from main stack, push B_expr to unify_stack
    //   B_expr = the conclusion of ax_2 = imp(imp(a,imp(M,a)), imp(imp(a,M),imp(a,a)))
    //          = imp(imp(a,imp(M,a)), C)
    //   unify_stack: [B_expr, C]
    //
    // UTerm(imp): pop B_expr, check head=imp ✓, push C, imp(a,imp(M,a))
    //   unify_stack: [imp(a,imp(M,a)), C, C]
    //
    // URef(0): pop imp(a,imp(M,a)), check = uheap[0] = imp(a,imp(M,a))
    //   Need pointer equality! uheap[0] = the arg1 we passed = Ref(5) = heap[5].
    //   The imp(a,imp(M,a)) from B_expr was built by Ref(5) in step B, giving
    //   the same heap[5] pointer. ✓
    //   unify_stack: [C, C]
    //
    // URef(1): pop C, check = uheap[1] = C (both from heap[7])
    //   But wait — the C in B_expr might be a different pointer.
    //   In step B, I built C using TermSave, which gives heap[7].
    //   Then the conclusion was built as Term(imp)(heap[5], heap[7]).
    //   Inside this conclusion expression, the second child is the same heap[7] pointer.
    //   When ax_2's Thm runs, it takes this conclusion as input. The Thm result
    //   |- B stores this conclusion expression. When UHyp pops |- B, it pushes
    //   the conclusion expression. When UTerm(imp) decomposes it, it gives back
    //   the same sub-expression pointers — including heap[7] for C.
    //
    //   And uheap[1] = arg2 passed to inner ax_mp = Ref(7) = heap[7].
    //   Same pointer! ✓
    //   unify_stack: [C]
    //
    // UHyp: pop |- A from main stack, push A_expr
    //   A_expr = imp(a, imp(M, a)) (from step A's Thm ax_1 result)
    //   unify_stack: [A_expr, C]
    //
    // URef(0): pop A_expr, check = uheap[0] = imp(a,imp(M,a))
    //   A_expr was built using the conclusion that was passed to Thm ax_1 in step A.
    //   That conclusion was heap[5] (from TermSave in step A).
    //   And uheap[0] = Ref(5) = heap[5]. Same pointer! ✓
    //
    //   Wait, but A_expr is |- A's inner expression. When Thm ax_1 ran, it received
    //   the conclusion expression (heap[5]) and returned |- heap[5]. So A_expr = heap[5].
    //   And uheap[0] = Ref(5) = heap[5]. Same pointer. ✓
    //   unify_stack: [C]
    //
    // URef(1): pop C, check = uheap[1] = C
    //   The C here is the original C from the conclusion we passed to inner ax_mp.
    //   The conclusion was Ref(7) = heap[7] = C.
    //   And uheap[1] = Ref(7) = heap[7] = C. Same pointer. ✓
    //   unify_stack: []
    //
    // Inner ax_mp unification passes! ✓
    //
    // After step C: stack = [|- D, |- C_result]
    // C_result = C = imp(imp(a,M), imp(a,a))  (the conclusion we passed)
    //
    // ── Step E: outer ax_mp ──
    //   Ref(3)     → [|- D, |- C, imp(a,M)]                       ← outer_arg1
    //   Ref(6)     → [|- D, |- C, imp(a,M), imp(a,a)]             ← outer_arg2
    //   Ref(6)     → [|- D, |- C, imp(a,M), imp(a,a), imp(a,a)]   ← outer_concl
    //   Thm(ax_mp) → pops imp(a,a), imp(a,a), imp(a,M)
    //                 uheap = [imp(a,M), imp(a,a)]
    //                 UHyp 1 pops |- C
    //                 UHyp 2 pops |- D
    //                 pushes |- imp(a,a)
    // Stack: [|- imp(a, a)] ✓
    //
    // Let me verify outer ax_mp unification:
    // uheap = [imp(a,M), imp(a,a)]
    //
    // unify_stack starts with: [imp(a,a)] (the concl)
    //
    // UHyp: pop |- C from main stack, push C_expr = C = imp(imp(a,M), imp(a,a))
    //   unify_stack: [C, imp(a,a)]
    //
    // UTerm(imp): pop C = imp(imp(a,M), imp(a,a)), push imp(a,a) and imp(a,M)
    //   unify_stack: [imp(a,M), imp(a,a), imp(a,a)]
    //
    // URef(0): pop imp(a,M), check = uheap[0] = imp(a,M)
    //   uheap[0] = Ref(3) = heap[3] = imp(a,M) built in step D.
    //   The imp(a,M) from C is a sub-expression of C (heap[7]).
    //   C was built as imp(heap[3], heap[6]) in step B.
    //   So the first sub-expression of C is heap[3]. ✓
    //   unify_stack: [imp(a,a), imp(a,a)]
    //
    // URef(1): pop imp(a,a), check = uheap[1] = imp(a,a)
    //   uheap[1] = Ref(6) = heap[6] = imp(a,a).
    //   The imp(a,a) from C is the second sub-expression = heap[6]. ✓
    //   unify_stack: [imp(a,a)]
    //
    // UHyp: pop |- D from main stack, push D_expr = imp(a, M)
    //   D_expr = the expression inside |- D = heap[3] (from ThmSave in step D)
    //   unify_stack: [imp(a,M), imp(a,a)]
    //
    // URef(0): pop imp(a,M), check = uheap[0] = imp(a,M) = heap[3]
    //   D_expr = heap[3], uheap[0] = heap[3]. Same pointer! ✓
    //   unify_stack: [imp(a,a)]
    //
    // URef(1): pop imp(a,a), check = uheap[1] = imp(a,a) = heap[6]
    //   This imp(a,a) is from the conclusion we passed = Ref(6) = heap[6].
    //   And uheap[1] = Ref(6) = heap[6]. Same pointer! ✓
    //   unify_stack: []
    //
    // Outer ax_mp unification passes! ✓
    //
    // DONE! The proof is |- imp(a, a). ✓
    //
    // Now the id theorem's unification checks that the proof result matches
    // the theorem statement imp(a, a).
    //
    // The proof result is |- imp(a,a), where the expression is the conclusion
    // from the outer ax_mp. The outer ax_mp's conclusion was Ref(6) = heap[6]
    // = imp(a,a) built in step B.
    //
    // The theorem's unify stream is: UTerm(imp), URef(0), URef(0)
    // unify_stack starts with: [imp(a,a)]
    // UTerm(imp): pop imp(a,a), push a, a
    // URef(0): pop a, check = uheap[0] = a. The uheap for the theorem has
    //   one arg (the a variable). In the proof, this is heap[0] = a.
    //   The a inside imp(a,a) = heap[6] was built from Ref(0) twice in step B,
    //   so both children are heap[0] = a. ✓
    // URef(0): pop a, check = uheap[0] = a ✓
    //
    // VERIFICATION COMPLETE! ✓

    // Heap starts: [a] (index 0)

    // ── Build helper terms and save to heap ──
    // Build not(a), M=imp(not(a),a), imp(a,M) for reuse
    ProofCmd::Ref(0).write_to(p)?;                                  // [a]
    ProofCmd::Ref(0).write_to(p)?;                                  // [a, a]
    ProofCmd::Term { tid: TERM_NOT, save: true }.write_to(p)?;      // [a, not(a)]  heap[1]=not(a)
    ProofCmd::Ref(1).write_to(p)?;                                  // [..., not(a)]
    ProofCmd::Ref(0).write_to(p)?;                                  // [..., a]
    ProofCmd::Term { tid: TERM_IMP, save: true }.write_to(p)?;      // [a, not(a), M]  heap[2]=M
    ProofCmd::Term { tid: TERM_IMP, save: true }.write_to(p)?;      // [a, imp(a,M)]  heap[3]=imp(a,M)

    // Now stack has [a, imp(a,M)] — these are leftovers from building.
    // We need to consume them. Let's use them as args for step D (ax_1).
    // Step D needs: [arg1=a, arg2=not(a), concl=imp(a,M)]
    // Stack is [a, imp(a,M)]. We need not(a) between them.
    // Hmm, that won't work. Let me restructure.
    //
    // Better: build helpers, then use a dummy Thm to consume stack leftovers.
    // Actually, the cleanest approach: DON'T leave anything on the stack.
    // Build helpers INSIDE a Thm call (as part of the conclusion expression).

    // Let me restart with a cleaner approach. I'll use Ref exclusively to
    // push from the heap, and build fresh for each Thm call.

    // Stack after above: [a, imp(a,M)]
    // I need to clean up. Let me use these as part of step D.
    // Step D = ax_1(a, not(a)): needs [arg1=a, arg2=not(a), concl=imp(a,M)]
    // Stack has [a, imp(a,M)]. I need to get not(a) in between.
    // Can't insert — must pop first. But no pop instruction!

    // RESTART: avoid leaving things on the stack. Build helpers differently.
    // Use step D to introduce helpers into the heap.

    // Actually, the easiest fix: start with step B which needs the most complex
    // expression and doesn't leave cleanup issues.
    //
    // I'll use a completely fresh approach — just build args+concl for each Thm
    // call from heap refs, no leftover stack entries.

    // But I need not(a) and M in the heap first! And building them puts them
    // on the stack. Unless I embed them in a Thm call.

    // SIMPLEST FIX: Use the first Thm call (step D) to both build the helpers
    // AND produce the proof. But step D's result needs to be at a specific
    // stack position (for the outer ax_mp). Let me just trace it through.

    // OK let me think about this from scratch with correct ordering.
    //
    // Required order: B (hyp1/bottom), A (hyp2/top), inner_mp, D (hyp2/top), outer_mp
    //
    // Step B = ax_2(a, M, a)
    // Step A = ax_1(a, M)
    // Step C = ax_mp (inner)
    // Step D = ax_1(a, not(a))
    // Step E = ax_mp (outer)
    //
    // I need not(a) and M in the heap BEFORE step B. I'll build them as part
    // of step D's args... no, step D comes AFTER B.
    //
    // I need to build helper expressions first, accepting that they stay on the stack,
    // and then consume them in the right order.

    // Plan: Build not(a), M, imp(a,M) and save to heap.
    // These will be on the stack, but the first Thm call will NOT consume them
    // as args (because they'll be below the args). This is OK — they'll just
    // sit below everything else until consumed by later Thm calls.
    //
    // Wait, that's dangerous. All Thm calls pop from the main stack for UHyp.
    // If there are stray expressions below, UHyp might pop them!
    //
    // For step B (ax_2, no hyps): no UHyp, so stray values below are fine.
    // For step A (ax_1, no hyps): same.
    // For step C (ax_mp, 2 hyps): UHyp pops |- A and |- B from stack. Below that
    //   are the stray helper expressions. They won't be popped because UHyp only
    //   runs twice (matching 2 hyps).
    // For step D (ax_1, no hyps): fine.
    // For step E (ax_mp, 2 hyps): UHyp pops |- D and |- C. Below are strays. Fine.
    //
    // But at the END, the stack must have exactly ONE element (the final proof).
    // If there are strays, the check will fail!
    //
    // So I CANNOT leave strays. I must consume everything.
    //
    // REAL SOLUTION: build the helpers and immediately consume them as args in a Thm.
    // The FIRST Thm call consumes them.
    //
    // But the first Thm is step B (ax_2), which doesn't need not(a) or imp(a,M) directly —
    // it needs a, M, a as args.
    //
    // Actually, step B DOES need M. So let me build M inline as part of step B's args.
    //
    // New plan:
    // 1. Build not(a) and M inside step B's arg setup.
    //    Push a (arg1), then build M for arg2, then push a (arg3), then build conclusion.
    //    All temps are consumed by the Term/Thm calls.

    // ── Step B: ax_2(a, M, a) ──
    // Build M = imp(not(a), a) inline, save to heap for later use.
    // args: a, M, a
    ProofCmd::Ref(0).write_to(p)?;                                  // [a]  ← arg1
    // Build M inline:
    ProofCmd::Ref(0).write_to(p)?;                                  // [a, a]
    ProofCmd::Term { tid: TERM_NOT, save: true }.write_to(p)?;      // [a, not(a)]  heap[1]=not(a)
    ProofCmd::Ref(0).write_to(p)?;                                  // [a, not(a), a]
    ProofCmd::Term { tid: TERM_IMP, save: true }.write_to(p)?;      // [a, M]  heap[2]=M, ← arg2
    ProofCmd::Ref(0).write_to(p)?;                                  // [a, M, a]  ← arg3
    // Build conclusion: imp(imp(a,imp(M,a)), imp(imp(a,M), imp(a,a)))
    // Part 1: imp(a, imp(M, a))
    ProofCmd::Ref(0).write_to(p)?;                                  // a
    ProofCmd::Ref(2).write_to(p)?;                                  // M
    ProofCmd::Ref(0).write_to(p)?;                                  // a
    ProofCmd::Term { tid: TERM_IMP, save: false }.write_to(p)?;     // imp(M, a)
    ProofCmd::Term { tid: TERM_IMP, save: true }.write_to(p)?;      // imp(a,imp(M,a))  heap[3]
    // Part 2: imp(imp(a,M), imp(a,a))
    ProofCmd::Ref(0).write_to(p)?;                                  // a
    ProofCmd::Ref(2).write_to(p)?;                                  // M
    ProofCmd::Term { tid: TERM_IMP, save: true }.write_to(p)?;      // imp(a,M)  heap[4]
    ProofCmd::Ref(0).write_to(p)?;                                  // a
    ProofCmd::Ref(0).write_to(p)?;                                  // a
    ProofCmd::Term { tid: TERM_IMP, save: true }.write_to(p)?;      // imp(a,a)  heap[5]
    ProofCmd::Term { tid: TERM_IMP, save: true }.write_to(p)?;      // imp(imp(a,M),imp(a,a))  heap[6]
    // Outer: imp(part1, part2)
    ProofCmd::Term { tid: TERM_IMP, save: false }.write_to(p)?;     // full conclusion
    ProofCmd::Thm { tid: THM_AX2, save: false }.write_to(p)?;      // [|- B]

    // ── Step A: ax_1(a, M) ──
    // args: a, M. conclusion: imp(a, imp(M, a)) = heap[3]
    ProofCmd::Ref(0).write_to(p)?;                                  // a  ← arg1
    ProofCmd::Ref(2).write_to(p)?;                                  // M  ← arg2
    ProofCmd::Ref(3).write_to(p)?;                                  // imp(a,imp(M,a))  ← concl
    ProofCmd::Thm { tid: THM_AX1, save: false }.write_to(p)?;      // [|- B, |- A]

    // ── Step C: inner ax_mp ──
    // args: imp(a,imp(M,a)), imp(imp(a,M),imp(a,a))
    // UHyp 1 pops |- A (top) — matches hyp2 = arg1 = imp(a,imp(M,a)) ✓
    // UHyp 2 pops |- B — matches hyp1 = imp(arg1, arg2) ✓
    ProofCmd::Ref(3).write_to(p)?;                                  // arg1 = imp(a,imp(M,a))
    ProofCmd::Ref(6).write_to(p)?;                                  // arg2 = imp(imp(a,M),imp(a,a))
    ProofCmd::Ref(6).write_to(p)?;                                  // concl = arg2 (same ptr)
    ProofCmd::Thm { tid: THM_AX_MP, save: false }.write_to(p)?;    // [|- C]

    // ── Step D: ax_1(a, not(a)) → |- imp(a, M) ──
    // args: a, not(a). conclusion: imp(a, imp(not(a), a)) = imp(a, M) = heap[4]
    ProofCmd::Ref(0).write_to(p)?;                                  // a  ← arg1
    ProofCmd::Ref(1).write_to(p)?;                                  // not(a)  ← arg2
    ProofCmd::Ref(4).write_to(p)?;                                  // imp(a,M)  ← concl
    ProofCmd::Thm { tid: THM_AX1, save: false }.write_to(p)?;      // [|- C, |- D]

    // ── Step E: outer ax_mp ──
    // args: imp(a,M), imp(a,a)
    // UHyp 1 pops |- D (top) — matches hyp2 = arg1 = imp(a,M) ✓
    // UHyp 2 pops |- C — matches hyp1 = imp(arg1, arg2) ✓
    ProofCmd::Ref(4).write_to(p)?;                                  // arg1 = imp(a,M)
    ProofCmd::Ref(5).write_to(p)?;                                  // arg2 = imp(a,a)
    ProofCmd::Ref(5).write_to(p)?;                                  // concl = imp(a,a)
    ProofCmd::Thm { tid: THM_AX_MP, save: false }.write_to(p)?;    // [|- imp(a,a)]

    Ok(())
}
