package org.kframework.kompile;

import java.util.List;

import org.kframework.kil.NonTerminal;
import org.kframework.kil.Production;

public class ThePair implements GlobalElement {
	// the left part of the "::="
	NonTerminal sort;
	// the right part of the "::="
	Production production;
	
	public ThePair(){
		
	}
	
	public void add(NonTerminal sort, Production production){
		
		this.sort = sort;
		this.production = production;
	}

	@Override
	public NonTerminal getResultSort() {
		// TODO Auto-generated method stub
		return sort;
	}

	@Override
	public List getSubSorts() {
		// TODO Auto-generated method stub
		return null;
	}
}
