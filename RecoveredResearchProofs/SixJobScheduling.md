# A six-job lower bound for non-clairvoyant scheduling with predictions

**Theorem.** For nonpreemptive makespan scheduling on two identical machines with prediction error at most $21/20$, every deterministic scheduler has worst-case ratio at least $31527/29600\approx 1.06510$. The bound holds even if the scheduler knows the error limit, may idle, and has only six jobs to schedule.

The old notes identified the six-job instance. The proof below verifies the bound in a stronger scheduling game that removes timing and gives the scheduler immediate feedback. The resulting lower bound is strictly above $841/800$, the lower bound of Bampis–Kononov–Lucarelli–Pascual evaluated at this error. It answers the tightness question at this error in the negative. The optimal ratio in the small-error regime remains open. This is a finite computer-assisted proof with a standard-library verifier. [Bampis et al., ISAAC 2023](https://doi.org/10.4230/LIPIcs.ISAAC.2023.9) · [Chen–Tan, Theorems 2.1 and 2.3](https://arxiv.org/html/2504.10945v1#S2)

## An assignment game

The input consists of three predictions equal to $1$ and three equal to $27/20$. Scale all numbers by 8400. The two possible true lengths are the endpoints of each allowed prediction interval. They are
$$
D_0=\{8000,8820\},\qquad D_1=\{10800,11907\}.
$$
At each step of the game the scheduler picks the prediction type of an unused job and chooses either machine, with no restriction based on the current loads. The adversary picks one of the two allowed lengths for that type. It is revealed immediately. The chosen duration is added to the load of the selected machine. With all six jobs assigned, the payoff is the larger load divided by the optimal offline two-way partition of their final lengths.

This game can simulate any deterministic nonpreemptive algorithm for the original instance. Given the lengths exposed by the game, run the original algorithm's clock virtually, disclosing a length to it only when the simulated job finishes. Each new start specifies a legal move of the game. Simultaneous starts can be processed in a fixed order, keeping the other simultaneous choices as the simulated algorithm made them. Whenever the original algorithm finishes all six jobs, its makespan is at least the larger of its two total assigned loads. The game uses the same offline denominator. Against a deterministic scheduler a response sequence fixes a particular valid six-job instance, and replay on that instance makes the same moves. Thus the value of the game is a lower bound for the original problem, including schedulers with arbitrary real start times.

## Exact recurrence and certificate

A state consists of the remaining job counts $(a_0,a_1)$, loads $(L_0,L_1)$, and the multiset $M$ of durations already assigned. For $i\in\{0,1\}$ with $a_i>0$ and $m\in\{0,1\}$, let $s(i,m,t)$ be the successor state that uses type $i$ on machine $m$ and adds duration $t$. The value satisfies
$$
V(s)=\min_{\substack{i:a_i>0\\m\in\{0,1\}}}\max_{t\in D_i} V(s(i,m,t)).
$$
At a terminal state it is
$$
V(s)=\frac{\max(L_0,L_1)}{\min_{P\subseteq M}\max(\sum P,\sum(M\setminus P))},
$$
where subsets are submultisets. This follows by backward induction, with the scheduler choosing first at every state. Equal-prediction jobs are interchangeable because the durations of unassigned jobs have no constraints under the adversary other than their prediction intervals.

The [exact verifier](check_scheduling_bound.py) enumerates all the indicated branches and all offline partitions. It gives the following values after the first job is placed and its duration is revealed. The machine name is irrelevant at that step.
| First prediction | Short endpoint | Long endpoint |
|---|---:|---:|
| $1$ | $30707/29600$ | $31527/29600$ |
| $27/20$ | $31527/29600$ | $1521/1480$ |

For either choice the adversary obtains at least $31527/29600$. The payoff at the initial state is exactly that value. Its excess over the prior lower bound is $41/2960$. The verifier also reproduces the archival value $681/640$ using predictions $1$ and $3/2$ with three jobs per type.
