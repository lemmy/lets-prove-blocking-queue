# Contributing Guidelines

## Adding a blocking queue

Check out the "tlaplus" folder for an example of what this all looks like.

One folder per blocking queue, one blocking queue per folder. If you're the first person uploading for your proof language, name the folder after your method. If someone else already submitted a proof, you should postpend your folder with what makes your proof special.

Your code should formally prove the total specification of the blocking queue. It must do this without any assumptions in the proof, and the proof must correct. Proving intermediate lemmas or ghost functions is fine, as are using already-proven primitives your language's standard library.

Along with your blocking queue, you should include a `readme.md` file. It should contain:
* The name of your tool, and a link to learn more about it.
* A description of the language. What does it look like? How does it work? What makes it different or special?
* A description of your proof. How does it work? What interesting language properties or verification techniques does it showcase?

That's pretty much it!
