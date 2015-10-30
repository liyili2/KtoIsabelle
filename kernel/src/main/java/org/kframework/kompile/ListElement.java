package org.kframework.kompile;

import java.util.*;

import org.kframework.kil.NonTerminal;

public class ListElement implements GlobalElement {
	String seperatorLabel;
	String isabelleSepLabel;
	String terminalLabel;
	String isabelleTermLabel;
	NonTerminal argument;
	NonTerminal result;
	boolean isStrict;
	
	public ListElement(String sep,String isabelleSep, String term, String isabelleTerm
			, NonTerminal a, NonTerminal r, boolean strict){
		seperatorLabel = sep;
		isabelleSepLabel = isabelleSep;
		terminalLabel = term;
		isabelleTermLabel = isabelleTerm;
		argument = a;
		result = r;
		this.isStrict = strict;
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
