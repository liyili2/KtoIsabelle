package org.kframework.kompile;

import java.util.*;

import org.kframework.kil.NonTerminal;

public class NormalElement implements GlobalElement {
	String klabel;
	String isabelleLabel;
	List<NonTerminal> arguments;
	NonTerminal result;
	List<Integer> strictPositions;
	
	public NormalElement(String k,String isabelleLabel, List<NonTerminal> a
			, NonTerminal r, List<Integer> st){
		klabel = k;
		this.isabelleLabel = isabelleLabel;
		arguments = a;
		result = r;
		strictPositions = st;
	}

	@Override
	public NonTerminal getResultSort() {
		// TODO Auto-generated method stub
		return result;
	}

	@Override
	public List getSubSorts() {
		// TODO Auto-generated method stub
		return arguments;
	}

	@Override
	public String getIsabelleLabel() {
		// TODO Auto-generated method stub
		return this.isabelleLabel;
	}
}
