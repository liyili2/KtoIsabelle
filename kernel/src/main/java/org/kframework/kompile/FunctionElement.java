package org.kframework.kompile;

import java.util.List;

import org.kframework.kil.NonTerminal;

public class FunctionElement implements GlobalElement {
	String klabel;
	List<NonTerminal> arguments;
	NonTerminal result;
	
	public FunctionElement(String k, List<NonTerminal> a, NonTerminal r){
		klabel = k;
		arguments = a;
		result = r;
	}
}
