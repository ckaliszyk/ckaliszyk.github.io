This is the accompanying material for the paper:

  Agent Hunt: Bounty Based Collaborative Autoformalization With LLM Agents

# The formalization

  The final version of the formalization is in the file: AlgTop.mg
  This includes all the proofs that were completed by the agents
  as well as all the Admitted ones that are in progress. It assumes
  the standard Megalodon Library and the results from the Topology
  section (General Topology) to be completed.

  In addition, we provide the Brouwer.mg file, that focuses on the
  Brouwer fixed-point theorem theorem as described in the paper.
  It is an excerpt of the AlgTop file, with the final result in
  the section that assumes thm54_5_pi1_circle as a hypothesis and
  all the Brower proofs completed with Qed.

# Documentation

  An HTML-rendered version of the development can be seen in AlgTop.html

# To verify the formalization

* Get Megalodon

  any recent version should work, for example: https://github.com/mgwiki/Megalodon

* Compile it and run:

    megalodon -ind topology.index AlgTop.mg
  and
    megalodon -ind topology.index Brouwer.mg

  To check the whole AlgTop development and to check the Brouwer fixedpoint development

# To inspect the actions of the agents

  The file "log.txt" has the complete history of the repository, with all the agent commit comments included

