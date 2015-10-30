package org.kframework.kompile;

import java.util.ArrayList;
import java.util.List;

import org.kframework.kil.NonTerminal;

public class SubSortElement implements GlobalElement {
	String isabelleLabel;
    NonTerminal argument;
	NonTerminal result;
	
	public SubSortElement(String con, NonTerminal a, NonTerminal r){
		this.isabelleLabel = con;
		argument = a;
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
		List<NonTerminal> result = new ArrayList<NonTerminal>();
		result.add(argument);
		return result;
	}
}
