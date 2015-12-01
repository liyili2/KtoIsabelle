package org.kframework.kompile;

import java.util.List;

import org.kframework.kil.NonTerminal;

public class FunctionElement implements GlobalElement {
	String klabel;
	String isabelleLabel;
	List<NonTerminal> arguments;
	NonTerminal result;
	
	public FunctionElement(String k,String isabelleLabel, List<NonTerminal> a, NonTerminal r){
		klabel = k;
		this.isabelleLabel = isabelleLabel;
		arguments = a;
		result = r;
	}

	@Override
	public NonTerminal getResultSort() {
		// TODO Auto-generated method stub
		return result;
	}

	@Override
	public List getSubSorts() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getIsabelleLabel() {
		// TODO Auto-generated method stub
		return isabelleLabel;
	}	
}
