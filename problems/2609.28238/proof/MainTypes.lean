import SecondOrder.MainFrontiers

set_option pp.explicit true in
#print SecondOrder.HvpBudgetFeasible
set_option pp.explicit true in
#print SecondOrder.HvpSolves
#check SecondOrder.lipschitzHessian_frontier
#check SecondOrder.richResponse_frontier
#check SecondOrder.holderHessian_frontier
#print axioms SecondOrder.lipschitzHessian_frontier
#print axioms SecondOrder.richResponse_frontier
#print axioms SecondOrder.holderHessian_frontier
