package leidenuniv.symbolicai;

import java.io.File;
import java.util.Collection;
import java.util.HashMap;
import java.util.Vector;

import leidenuniv.symbolicai.environment.Maze;
import leidenuniv.symbolicai.logic.KB;
import leidenuniv.symbolicai.logic.Predicate;
import leidenuniv.symbolicai.logic.Sentence;
import leidenuniv.symbolicai.logic.Term;

public class MyAgent extends Agent {

	@Override
	public KB forwardChain(KB kb) {
		//This method should perform a forward chaining on the kb given as argument, until no new facts are added to the KB.
		//It starts with an empty list of facts. When ready, it returns a new KB of ground facts (bounded).
		//The resulting KB includes all deduced predicates, actions, additions and deletions, and goals.
		//These are then processed by processFacts() (which is already implemented for you)
		//HINT: You should assume that forwardChain only allows *bound* predicates to be added to the facts list for now.

		KB knowledgeBase = new KB();
		HashMap<String, Predicate> facts = new HashMap<>();

		for(Sentence s : kb.rules()) {
			Vector<Predicate> conditions = s.conditions;
			Vector<Predicate> conclusions = s.conclusions;
			if (conditions.isEmpty()) {
				facts.put(conclusions.get(0).toString(), conclusions.get(0));
			}
		}
		for (Sentence s : kb.rules()) {
			Vector<Predicate> conditions = s.conditions;
			Vector<Predicate> conclusions = s.conclusions;
			if (conditions.isEmpty())
				continue;
			Collection<HashMap<String, String>> substitutions = new Vector<HashMap<String, String>>();
			if (findAllSubstitutions(substitutions, new HashMap<String, String>(), s.conditions, facts)) {
				for (HashMap<String, String> substitution : substitutions) {
					for (Predicate conclusion : conclusions) {
						//If con is adopt and is in kb.rules/fact
						conclusion = substitute(conclusion, substitution);
						if (kb.contains(new Sentence(conclusion.toString())) && conclusion.adopt)
							continue;
						knowledgeBase.add(new Sentence(conclusion.toString()));
						facts.put(conclusion.toString(), conclusion);
					}
				}
			}
		}
		System.out.println("\n"+knowledgeBase.rules());
		return knowledgeBase;
	}

	@Override
	public boolean findAllSubstitutions(Collection<HashMap<String, String>> allSubstitutions,
										HashMap<String, String> substitution, Vector<Predicate> conditions, HashMap<String, Predicate> facts) {
		//Recursive method to find *all* valid substitutions for a vector of conditions, given a set of facts
		//The recursion is over Vector<Predicate> conditions (so this vector gets shorter and shorter, the farther you are with finding substitutions)
		//It returns true if at least one substitution is found (can be the empty substitution, if nothing needs to be substituted to unify the conditions with the facts)
		//allSubstitutions is a list of all substitutions that are found, which was passed by reference (so you use it build the list of substitutions)
		//substitution is the one we are currently building recursively.
		//conditions is the list of conditions you still need to find a substitution for (this list shrinks the further you get in the recursion).
		//facts is the list of predicates you need to match against (find substitutions so that a predicate form the conditions unifies with a fact)

		// Base case - We add substitution to allSubstitutions if conditions is empty (and we did not get any false before)
		if (conditions.isEmpty()) {
			allSubstitutions.add(substitution);
			return true;
		}

		// Case to check if it is negation/inequality/equality and if there are still more predicates and add it to the end
		for (int i=0; i<conditions.size();i++){
			Predicate condition = conditions.get(i);
			if (condition.not || condition.eql || condition.neg) {
				conditions.remove(i);
				conditions.add(condition);
			}
		}

		// Take the condition to evaluate in current recursion step
		Predicate condition = conditions.get(0);
		Vector<Predicate> curr_conditions = new Vector<Predicate>(conditions);
		curr_conditions.remove(0);
		boolean foundSubstitution = false;


		// After evaluating every predicate, evaluate its negation (Case where the predicate is a negation in the end)
		if (condition.neg) {
			Predicate temp = new Predicate(condition.toString().substring(1));;
			temp = substitute(temp, substitution);
			if (facts.containsKey(temp.toString())) {
				return false;
			}
			else
				foundSubstitution = findAllSubstitutions(allSubstitutions, substitution, curr_conditions, facts);
		}
		// After evaluating every predicate, evaluate its equality or inequality (Case where the predicate is an equality/inequality in the end)
		else if (condition.not || condition.eql) {
			// Get substitution from substitution variable for every variable in the equality/inequality predicate
			String sub_term1 = condition.getTerm(0).toString();
			sub_term1 = substitution.containsKey(sub_term1) ? substitution.get(sub_term1) : sub_term1;

			String sub_term2 = condition.getTerm(1).toString();
			sub_term2 = substitution.containsKey(sub_term2) ? substitution.get(sub_term2) : sub_term2;

			// If the inequality/equality does not satisfy given substitutions return false (otherwise if they are equal/not equal go to the next recursion)
			if (!((condition.not && sub_term1.equals(sub_term2)) || (condition.eql && !sub_term1.equals(sub_term2))))
				foundSubstitution = findAllSubstitutions(allSubstitutions, substitution, curr_conditions, facts);
		}
		// Case where there are normal predicates
		else {
			// Iterate over all facts to find a match with the current condition
			for (Predicate fact : facts.values()) {
				// For every fact check if there is unification with current condition
				HashMap<String, String> unifications = unifiesWith(condition, fact);
				if (unifications != null) {
					// Create a new map to hold the current substitution, copying from substitution map
					HashMap<String, String> curr_substitution = new HashMap<>(substitution);
					boolean incorrect = false;
					// Iterate each term in the unification to ensure no conflicts with the current substitution
					for (String term : unifications.keySet()) {
						// If the current term already exists in the current substitution but with a different value then it is incorrect
						if (curr_substitution.containsKey(term) && !curr_substitution.get(term).equals(unifications.get(term))) {
							incorrect = true;
							break;
						}
						// Otherwise add the new term and its value to the current substitution
						else curr_substitution.put(term, unifications.get(term));
					}
					// Next step in recursion (If we find substitution, we return true
					if (!incorrect && findAllSubstitutions(allSubstitutions, curr_substitution, curr_conditions, facts))
						foundSubstitution = true;
				}
			}
			// Add current condition again into conditions list
		}
		// Return whether any substitutions were successfully found
		return foundSubstitution;
	}

	@Override
	public HashMap<String, String> unifiesWith(Predicate p, Predicate f) {
		//Returns the valid substitution for which p predicate unifies with f
		//You may assume that Predicate f is fully bound (i.e., it has no variables anymore)
		//The result can be an empty substitution, if no substitution is needed to unify p with f (e.g., if p an f contain the same constants or do not have any terms)
		//Please note because f is bound and p potentially contains the variables, unifiesWith is NOT symmetrical
		//So: unifiesWith("human(X)","human(joost)") returns X=joost, while unifiesWith("human(joost)","human(X)") returns null
		//If no substitution is found it returns null

		// Create empty solutions
		HashMap<String, String> result = new HashMap<String, String>();
		// Check if same predicate
		if (p.getTerms().size() != f.getTerms().size() || !p.getName().equals(f.getName()))
			return null;
		// If they are actions they cannot be unified
		if (p.isAction() || f.isAction())
			return null;
		// Go over all terms
		for (int i = 0; i < p.getTerms().size(); i++) {
			Term pTerm = p.getTerm(i);
			Term fTerm = f.getTerm(i);
			// If it is not a variable and the terms are unequal, then unification is not possible
			if (!pTerm.var) {
				if (!pTerm.toString().equals(fTerm.toString()))
					return null;
			}
			// Check if both are terms and they are different or both are variables and return null
			else if (result.containsKey(pTerm.toString()) && !result.get(pTerm.toString()).equals(fTerm.toString()) || pTerm.var && fTerm.var)
				return null;
				// If every case that does not unify then add it
			else
				result.put(pTerm.toString(), fTerm.toString());
		}
		return result;
	}

	@Override
	public Predicate substitute(Predicate old, HashMap<String, String> s) {
		// Substitutes all variable terms in predicate <old> for values in substitution <s>
		//(only if a key is present in s matching the variable name of course)
		//Use Term.substitute(s)

		Predicate new_predicate = new Predicate(old.toString());
		for (Term each_term : new_predicate.getTerms())
			each_term.substitute(s);
		return new_predicate;
	}

	@Override
	public Plan idSearch(int maxDepth, KB kb, Predicate goal) {
		//The main iterative deepening loop
		//Returns a plan, when the depthFirst call returns a plan for depth d.
		//Ends at maxDepth
		//Predicate goal is the goal predicate to find a plan for.
		//Return null if no plan is found.

		for(int depth = 1; depth <= maxDepth; depth++) {
			Plan result = depthFirst(depth, 0, kb, goal, new Plan());
			if(result != null)
				return result;
		}
		return null;
	}

	@Override
	public Plan depthFirst(int maxDepth, int depth, KB state, Predicate goal, Plan partialPlan) {
		//Performs a depthFirst search for a plan to get to Predicate goal
		//Is a recursive function, with each call a deeper action in the plan, building up the partialPlan
		//Caps when maxDepth=depth
		//Returns (bubbles back through recursion) the plan when the state entails the goal predicate
		//Returns null if capped or if there are no (more) actions to perform in one node (state)
		//HINT: make use of think() and act() using the local state for the node in the search you are in.
		if(state.contains(goal))
			return partialPlan;

		if(depth >= maxDepth) {
			return null;
		}

		KB curr_state = new KB();
		for (Sentence s : state.rules())
			curr_state.add(s);

		KB desires_n = new KB();
		KB intentions_n = new KB();
		desires_n.add(new Sentence(goal.toString()));

		think(curr_state, desires_n, intentions_n);

		for (Sentence intention : intentions_n.rules()) {

			KB new_kb = new KB();
			for (Sentence s : state.rules())
				new_kb.add(s);
			act(null, intention.conclusions.get(0), new_kb, desires_n);

			Plan plan = new Plan(partialPlan);
			plan.add(intention);

			Plan finalPlan = depthFirst(maxDepth, depth + 1, new_kb, goal, plan);

			if (finalPlan != null)
				return finalPlan;

		}
		return null;
	}
}