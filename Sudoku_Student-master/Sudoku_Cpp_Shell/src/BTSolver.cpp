#include"BTSolver.hpp"

using namespace std;

// =====================================================================
// Constructors
// =====================================================================

BTSolver::BTSolver ( SudokuBoard input, Trail* _trail,  string val_sh, string var_sh, string cc )
: sudokuGrid( input.get_p(), input.get_q(), input.get_board() ), network( input )
{
	valHeuristics = val_sh;
	varHeuristics = var_sh;
	cChecks =  cc;

	trail = _trail;
}

// =====================================================================
// Consistency Checks
// =====================================================================

// Basic consistency check, no propagation done
bool BTSolver::assignmentsCheck ( void )
{
	for ( Constraint c : network.getConstraints() )
		if ( ! c.isConsistent() )
			return false;

	return true;
}

// =================================================================
// Arc Consistency
// =================================================================
bool BTSolver::arcConsistency ( void )
{
    vector<Variable*> toAssign;
    vector<Constraint*> RMC = network.getModifiedConstraints();
    for (int i = 0; i < RMC.size(); ++i)
    {
        vector<Variable*> LV = RMC[i]->vars;
        for (int j = 0; j < LV.size(); ++j)
        {
            if(LV[j]->isAssigned())
            {
                vector<Variable*> Neighbors = network.getNeighborsOfVariable(LV[j]);
                int assignedValue = LV[j]->getAssignment();
                for (int k = 0; k < Neighbors.size(); ++k)
                {
                    Domain D = Neighbors[k]->getDomain();
                    if(D.contains(assignedValue))
                    {
                        if (D.size() == 1)
                            return false;
                        if (D.size() == 2)
                            toAssign.push_back(Neighbors[k]);
                        trail->push(Neighbors[k]);
                        Neighbors[k]->removeValueFromDomain(assignedValue);
                    }
                }
            }
        }
    }
    if (!toAssign.empty())
    {
        for (int i = 0; i < toAssign.size(); ++i)
        {
            Domain D = toAssign[i]->getDomain();
            vector<int> assign = D.getValues();
            trail->push(toAssign[i]);
            toAssign[i]->assignValue(assign[0]);
        }
        return arcConsistency();
    }
    return network.isConsistent();
}

/**
 * Part 1 TODO: Implement the Forward Checking Heuristic
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *     the square's neighbors.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all MODIFIED variables, mapped to their MODIFIED domain. 
 * 		   The bool is true if assignment is consistent, false otherwise.
 */
pair<map<Variable*,Domain>,bool> BTSolver::forwardChecking ( void )
{
	/**
	 * Each time value is assigned to a var, that value is removed from domain of
	 * free variables in same line, same column, or say square
	*/
	map<Variable*, Domain> modifiedVars;
	ConstraintNetwork::VariableSet variables = network.getVariables();
	ConstraintNetwork::VariableSet c;
	for(Variable* v : variables){
		if(v->isModified()){
			c.push_back(v);
			v->setModified(false);
		}
	}

	for (Variable* var : c)
	{
		int val = var->getAssignment(); // getting value of var

		// iterate through neighbours to remove value from their domain
		for(Variable* neighbour : network.getNeighborsOfVariable(var)){
			Domain neighbourDom = neighbour->getDomain();
			if(neighbourDom.contains(val)){
				if(neighbour->isAssigned()){
					return make_pair(modifiedVars, false);
				}
				trail->push(neighbour);
				neighbour->removeValueFromDomain(val);
				modifiedVars[neighbour] = neighbourDom;
			}
		}
		
		if(!network.isConsistent()){
			return make_pair(modifiedVars, false);
		}
	}

	return make_pair(modifiedVars, true);
}

/**
 * Part 2 TODO: Implement both of Norvig's Heuristics
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *     the square's neighbors.
 *
 * (2) If a constraint has only one possible place for a value
 *     then put the value there.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all variables that were assigned during 
 *         the whole NorvigCheck propagation, and mapped to the values that they were assigned. 
 *         The bool is true if assignment is consistent, false otherwise.
 */
pair<map<Variable*,int>,bool> BTSolver::norvigCheck ( void )
{
	map<Variable*,int> assignedVars;

	// part 1: if var assigned, eliminate that value from square's neighbours
	ConstraintNetwork::VariableSet variables = network.getVariables();
	ConstraintNetwork::VariableSet modifiedVars;
	for(Variable* v : variables){
		if(v->isModified()){
			modifiedVars.push_back(v);
			v->setModified(false);
		}
	}

	for (Variable* var : modifiedVars)
	{
		int val = var->getAssignment(); // getting value of var

		// iterate through neighbours to remove value from their domain
		for(Variable* neighbour : network.getNeighborsOfVariable(var)){
			Domain neighbourDom = neighbour->getDomain();
			if(neighbourDom.contains(val)){
				if(neighbour->isAssigned()){
					return make_pair(assignedVars, false);
				}
				trail->push(neighbour);
				neighbour->removeValueFromDomain(val);
			}
		}
	}

	// part 2: if a constraint has only one possible place for a value then put the value there

	// sudoku board: sudokuGrid

	ConstraintNetwork::ConstraintSet constraints = network.getConstraints();
	for(Constraint c : constraints){
		for(int i = 1; i <= 9; i++){
			int avail_pos_count = 0;
			Variable* toAssign;
			for(Variable* v : c.vars){
				if(v->getDomain().contains(i)){
					avail_pos_count++;
					toAssign = v;
				}
			}
			if(avail_pos_count == 0){
				return make_pair(assignedVars, false);
			}
			if(avail_pos_count == 1){
				trail->push(toAssign);
				toAssign->assignValue(i);
				if(!network.isConsistent()){
					return make_pair(assignedVars, false);
				}
			}
		}
	}
    return make_pair(assignedVars, network.isConsistent());
}

/**
 * Optional TODO: Implement your own advanced Constraint Propagation
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
bool BTSolver::getTournCC ( void )
{
	return false;
}

// =====================================================================
// Variable Selectors
// =====================================================================

// Basic variable selector, returns first unassigned variable
Variable* BTSolver::getfirstUnassignedVariable ( void )
{
	for ( Variable* v : network.getVariables() )
		if ( !(v->isAssigned()) )
			return v;

	// Everything is assigned
	return nullptr;
}

/**
 * Part 1 TODO: Implement the Minimum Remaining Value Heuristic
 *
 * Return: The unassigned variable with the smallest domain
 */
Variable* BTSolver::getMRV ( void )
{
	ConstraintNetwork::VariableSet vars = network.getVariables();

	ConstraintNetwork::VariableSet unassignedVars; // set of unassigned variables
	for(Variable* v : vars){
		if(v->getAssignment() == 0){
			unassignedVars.push_back(v); 
		}
	}

	// if no unassigned variables, return null
	if(unassignedVars.size() == 0){
		return nullptr;
	}

	// find variable with smallest domain
	Variable* retVar = unassignedVars[0];
	int minDomain = retVar->getDomain().size();
	for(Variable* v : unassignedVars){
		int compare = v->getDomain().size();
		if(compare < minDomain){
			minDomain = compare;
			retVar = v;
		}
	}

    return retVar;
}

/**
 * Part 2 TODO: Implement the Minimum Remaining Value Heuristic
 *                with Degree Heuristic as a Tie Breaker
 *
 * Return: The unassigned variable with the smallest domain and affecting the most unassigned neighbors.
 * 		   If there are multiple variables that have the same smallest domain with the same number 
 * 		   of unassigned neighbors, add them to the vector of Variables.
 *         If there is only one variable, return the vector of size 1 containing that variable.
 */
vector<Variable*> BTSolver::MRVwithTieBreaker ( void )
{
	vector<Variable*> retVec;

	ConstraintNetwork::VariableSet variables = network.getVariables();
	ConstraintNetwork::VariableSet unassignedVars;
	for(Variable* v : variables){
		if(!v->isAssigned()){
			unassignedVars.push_back(v);
		}
	}

	if(unassignedVars.size() == 0){
		retVec.push_back(nullptr);
		return retVec;
	}

	 
	
	Variable* minVar = unassignedVars[0];
	int minDomSize = minVar->size();
	int maxNeighboursAffected;
	ConstraintNetwork::VariableSet neighbours = network.getNeighborsOfVariable(minVar);

	for(Variable* neighbour : neighbours){
		if(!neighbour->isAssigned()){
			maxNeighboursAffected++;
		}
	}

	for(Variable* u : unassignedVars){
		int currNeighboursAffected;
		neighbours = network.getNeighborsOfVariable(u);
		for(Variable* neighbour : neighbours){
			if(!neighbour->isAssigned()){
				currNeighboursAffected++;
			}
		}
		if(u->size() < minDomSize && currNeighboursAffected > maxNeighboursAffected){
			minDomSize = u->size();
			maxNeighboursAffected = currNeighboursAffected;
			minVar = u;
		}
	}

	for(Variable* u : unassignedVars){
		int currNeighboursAffected;
		neighbours = network.getNeighborsOfVariable(u);
		for(Variable* neighbour : neighbours){
			if(!neighbour->isAssigned()){
				currNeighboursAffected++;
			}
		}

		if(u->size() == minDomSize && currNeighboursAffected == maxNeighboursAffected){
			retVec.push_back(u);
		}
	}

    return retVec;
}

/**
 * Optional TODO: Implement your own advanced Variable Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
Variable* BTSolver::getTournVar ( void )
{
	return nullptr;
}

// =====================================================================
// Value Selectors
// =====================================================================

// Default Value Ordering
vector<int> BTSolver::getValuesInOrder ( Variable* v )
{
	vector<int> values = v->getDomain().getValues();
	sort( values.begin(), values.end() );
	return values;
}

/**
 * Part 1 TODO: Implement the Least Constraining Value Heuristic
 *
 * The Least constraining value is the one that will knock the least
 * values out of it's neighbors domain.
 *
 * Return: A list of v's domain sorted by the LCV heuristic
 *         The LCV is first and the MCV is last
 */
vector<int> BTSolver::getValuesLCVOrder ( Variable* v )
{
	vector<int> ret_vec = vector<int>();

	Domain::ValueSet vals = v->getDomain().getValues();

	// check how many neighbours each value will knock out
	vector<Variable*> neighbours = network.getNeighborsOfVariable(v);
	vector<pair<int, int>> neighboursKnockedOut;
	for(int val : vals){
		int count = 0;
		for(Variable* n : neighbours){
			if(n->getDomain().contains(val)){
				count++;
			}
		}
		pair<int, int> pushVal(count, val);
		neighboursKnockedOut.push_back(pushVal);
	}

	sort(neighboursKnockedOut.begin(), neighboursKnockedOut.end());

	// testing neighboursKnockedOut
	// for(auto c : neighboursKnockedOut){
	// 	cout << c.first << ' ';
	// }
	// cout << endl;

	for(pair<int, int> p : neighboursKnockedOut){
		ret_vec.push_back(p.second);
	}

    return ret_vec;
}

/**
 * Optional TODO: Implement your own advanced Value Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
vector<int> BTSolver::getTournVal ( Variable* v )
{
	return vector<int>();
}

// =====================================================================
// Engine Functions
// =====================================================================

int BTSolver::solve ( float time_left)
{
	if (time_left <= 60.0)
		return -1;
	double elapsed_time = 0.0;
    clock_t begin_clock = clock();

	if ( hasSolution )
		return 0;

	// Variable Selection
	Variable* v = selectNextVariable();

	if ( v == nullptr )
	{
		for ( Variable* var : network.getVariables() )
		{
			// If all variables haven't been assigned
			if ( ! ( var->isAssigned() ) )
			{
				return 0;
			}
		}

		// Success
		hasSolution = true;
		return 0;
	}

	// Attempt to assign a value
	for ( int i : getNextValues( v ) )
	{
		// Store place in trail and push variable's state on trail
		trail->placeTrailMarker();
		trail->push( v );

		// Assign the value
		v->assignValue( i );

		// Propagate constraints, check consistency, recurse
		if ( checkConsistency() ) {
			clock_t end_clock = clock();
			elapsed_time += (float)(end_clock - begin_clock)/ CLOCKS_PER_SEC;
			double new_start_time = time_left - elapsed_time;
			int check_status = solve(new_start_time);
			if(check_status == -1) {
			    return -1;
			}
			
		}

		// If this assignment succeeded, return
		if ( hasSolution )
			return 0;

		// Otherwise backtrack
		trail->undo();
	}
	return 0;
}

bool BTSolver::checkConsistency ( void )
{
	if ( cChecks == "forwardChecking" )
		return forwardChecking().second;

	if ( cChecks == "norvigCheck" )
		return norvigCheck().second;

	if ( cChecks == "tournCC" )
		return getTournCC();

	return assignmentsCheck();
}

Variable* BTSolver::selectNextVariable ( void )
{
	if ( varHeuristics == "MinimumRemainingValue" )
		return getMRV();

	if ( varHeuristics == "MRVwithTieBreaker" )
		return MRVwithTieBreaker()[0];

	if ( varHeuristics == "tournVar" )
		return getTournVar();

	return getfirstUnassignedVariable();
}

vector<int> BTSolver::getNextValues ( Variable* v )
{
	if ( valHeuristics == "LeastConstrainingValue" )
		return getValuesLCVOrder( v );

	if ( valHeuristics == "tournVal" )
		return getTournVal( v );

	return getValuesInOrder( v );
}

bool BTSolver::haveSolution ( void )
{
	return hasSolution;
}

SudokuBoard BTSolver::getSolution ( void )
{
	return network.toSudokuBoard ( sudokuGrid.get_p(), sudokuGrid.get_q() );
}

ConstraintNetwork BTSolver::getNetwork ( void )
{
	return network;
}
