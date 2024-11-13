package leidenuniv.symbolicai;

import java.util.Collection;
import java.util.HashMap;
import java.util.Set;
import java.util.Vector;

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
		
		return null;
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

		if (conditions.isEmpty()) {
			allSubstitutions.add(new HashMap<>(substitution));
			return true;
		}

		boolean foundSubstitution = false;
		Predicate condition = conditions.remove(0);

		if(condition.not || condition.eql) {
			if(!conditions.isEmpty()) {
				conditions.add(condition);
				foundSubstitution = findAllSubstitutions(allSubstitutions, substitution, conditions, facts);
			}
			else {
				String substituted_term1 = condition.getTerm(0).toString();
				substituted_term1 = substitution.containsKey(substituted_term1) ? substitution.get(substituted_term1) : substituted_term1;

				String substituted_term2 = condition.getTerm(1).toString();
				substituted_term2 = substitution.containsKey(substituted_term2) ? substitution.get(substituted_term2) : substituted_term2;

				if(!((condition.not && substituted_term1.equals(substituted_term2)) || (condition.eql && !substituted_term1.equals(substituted_term2))))
					foundSubstitution = findAllSubstitutions(allSubstitutions, substitution, conditions, facts);
				conditions.insertElementAt(condition, 0);
			}
		}
		else {
			for(Predicate fact: facts.values()) {
				HashMap<String, String> unifications = unifiesWith(condition, fact);
				if (unifications != null) {
					Set<String> temp = new HashMap<String,String>(substitution).keySet();
					for (String term: unifications.keySet()) {
						if (!substitution.containsKey(term))
							substitution.put(term, unifications.get(term));
						else if (!substitution.get(term).equals(unifications.get(term))) {
							for (String terminate_term : unifications.keySet())
								if (!temp.contains(terminate_term))
									substitution.remove(terminate_term);
							conditions.insertElementAt(condition, 0);
							return false;
						}
					}
					if(findAllSubstitutions(allSubstitutions, substitution, conditions, facts))
						foundSubstitution = true;
					for (String terminate_term : unifications.keySet())
						if (!temp.contains(terminate_term))
		                	substitution.remove(terminate_term);
				}			
				
			}
			conditions.insertElementAt(condition, 0);
		}
		System.out.println("\n"+allSubstitutions);
		
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
		
		HashMap<String, String> result = new HashMap<String, String>();
		if(p.getTerms().size() == f.getTerms().size() && p.getName().compareTo(f.getName())==0 && p.getTerms().size() != 0) {
			for(int i=0;i < p.getTerms().size();i++) {
				if(p.getTerm(i).var && !f.getTerm(i).var)
					result.put(p.getTerm(i).toString(), f.getTerm(i).toString());
				if(!p.getTerm(i).var && !f.getTerm(i).var && p.getTerm(i).toString().compareTo(f.getTerm(i).toString())!=0)
					return null;
			}
			return result;
		}
		
		return null;
	}

	@Override
	public Predicate substitute(Predicate old, HashMap<String, String> s) {
		// Substitutes all variable terms in predicate <old> for values in substitution <s>
		//(only if a key is present in s matching the variable name of course)
		//Use Term.substitute(s)
		Vector<Term> old_terms = old.getTerms();
		String substituted_string = old.getName() + "(";
		for(Term x: old_terms) {
			x.substitute(s);
			substituted_string += x + ",";
		}
		substituted_string = substituted_string.substring(0, substituted_string.length() - 1) + ")";
		Predicate substituted_pred = new Predicate(substituted_string);
		substituted_pred.not = old.not;
		substituted_pred.eql = old.eql;
		substituted_pred.add = old.add;
		substituted_pred.del = old.del;
		substituted_pred.act = old.act;
		substituted_pred.adopt = old.adopt;
		substituted_pred.drop = old.drop;
		substituted_pred.neg = old.neg;
		return substituted_pred;
	}

	@Override
	public Plan idSearch(int maxDepth, KB kb, Predicate goal) {
		//The main iterative deepening loop
		//Returns a plan, when the depthFirst call returns a plan for depth d.
		//Ends at maxDepth
		//Predicate goal is the goal predicate to find a plan for.
		//Return null if no plan is found.
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
		return null;
	}
}
