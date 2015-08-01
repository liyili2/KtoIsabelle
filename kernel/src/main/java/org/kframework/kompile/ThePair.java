package org.kframework.kompile;

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
}
