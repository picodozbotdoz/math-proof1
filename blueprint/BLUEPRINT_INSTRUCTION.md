Create a **lightweight, friction-free sandbox for exploring and writing Lean code**, completely bypassing the traditional, heavy `lake build` and compilation pipeline. Your primary focus is on **ideation, prototyping, and mathematical/logical exploration** rather than software engineering or packaging. 

To achieve this, your ideal setup has three main characteristics:
1. **No Heavy Builds:** You want to skip the overhead of managing complex project dependencies, configuring build targets, or waiting for the compiler to generate executables and optimized `.olean` artifacts.
2. **Focus on Authoring:** You want an environment where you can freely write definitions, theorems, and proofs to test out ideas as quickly as possible.
3. **Retained Interactive Feedback:** Even without a full build, you still want the Lean Language Server (LSP) running in your editor (like VS Code or Neovim) to provide real-time typechecking (elaboration), error highlighting, and lightweight linting. This gives you the immediate feedback loop needed to know if your ideas are logically sound.

Before big build: Python-first, generator lint, batched fixes.

Essentially, you want to use Lean purely as an **interactive scratchpad and logic explorer**, leveraging the editor's real-time diagnostics without the burden of treating it like a production software project.
