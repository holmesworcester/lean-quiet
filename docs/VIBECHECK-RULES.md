# Vibecheck Rules

We evaluate submissions according to two primary axes:

1. **Coolness.** Is your project *cool*? Specifically, is it something your mom might think is cool? Here, we are explicitly _not_ looking for a b2b SAAS. We want to see consumer products -- things with GUIs, such as a video game, a menstrual tracker, a shader designer, a midi keyboard controller, a photo editor, an alarm clock app you pay to snooze, or a robot that can play socker.  This does not need to be totally consumer based product, but it needs to be something you can meaningfully demo to a reasonably nontechnical person and have them authentically go "ooh" without their eyes glossing over.
2. **Verification.** How meaningful is your formal verification of the product?  Did you prove important properties (relating to security, reliability, correctness, etc.) or just a huge quantity of mediocre, uninteresting properties?  Are your proofs relating to the code itself, a static translation of the code (for example using a formal semantics), a hand-written model of the code, or an AI-written model of the code? If it is a model, how, if at all, did you gain assurance that the model matches the actual code?  Do your proofs pass Comparator?

We **strongly** encourage you to write as much of your program code as possible in Lean, and to prove your code is correct in Lean.  This vastly simplifies the project, compared to writing the code in Rust or Golang and then needing to somehow "lift" it into Lean, for instance using a formal semantics.  However, if you really want to do something else -- such as using Bend, or writing your code in Rust and verifying it using Lean with Aeneas -- you can do so.

We will judge you based on the work you complete during the hackathon.  For example, if you build an entirely new app from scratch, and formally verify it, then we will expect less verification work from you, compared to if you come with a pre-existing or FOSS application and verify that.

We will award several special prizes. For example, a prize for the best physical object associated with a demo (such as a robot or a midi keyboard), or a (comedic) prize for the funniest possible Lean mistake.

You need to have a Makefile with "install" and "run" targets. So, if I clone your repo and do `make install && make run` it should "just work".

We reserve the right to make changes to the rules as needed, but will announce them when it happens.
