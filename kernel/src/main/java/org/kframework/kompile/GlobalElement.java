package org.kframework.kompile;

import java.util.List;

import org.kframework.kil.NonTerminal;

public interface GlobalElement {
	public NonTerminal getResultSort();
	public List<NonTerminal> getSubSorts();
}
