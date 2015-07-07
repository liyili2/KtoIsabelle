package org.kframework.kompile;

import java.util.ArrayList;
import java.util.Map;
import java.util.Map.Entry;

import org.kframework.kil.Bag;
import org.kframework.kil.BoolBuiltin;
import org.kframework.kil.Cell;
import org.kframework.kil.Collection;
import org.kframework.kil.FloatBuiltin;
import org.kframework.kil.IntBuiltin;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KSequence;
import org.kframework.kil.ListBuiltin;
import org.kframework.kil.ListTerminator;
import org.kframework.kil.MapBuiltin;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.SetBuiltin;
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Terminal;
import org.kframework.kil.Token;
import org.kframework.kil.UserList;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.NonCachingVisitor;
import org.kframework.utils.ColorUtil;

public class PrinterToIsabelle extends NonCachingVisitor {

	private int counter = 0;
	private int varCounter = 0;
	public PrinterToIsabelle(Context context) {
		super(context);
		// TODO Auto-generated constructor stub
	}
	
	private String getGenVar(){
		varCounter ++;
		return "generatedVar"+varCounter;
	}
	
    public Void visit(Term node, Void _void) {
    	if(node instanceof Rewrite){
    		this.visit((Rewrite)node, _void);
    	} else if(node instanceof Cell){
    		this.visit((Cell)node, _void);
    	} else if(node instanceof KApp){
    		this.visit((KApp)node, _void);
    	} else if(node instanceof Bag){
    		this.visit((Bag)node, _void);
    	} else if(node instanceof TermCons){
    		this.visit((TermCons)node, _void);
    	} else if(node instanceof KSequence) {
    		this.visit((KSequence)node, _void);
    	} else if(node instanceof Variable){
    		this.visit((Variable)node, _void);
    	} else if(node instanceof ListTerminator){
    		this.visit((ListTerminator)node, _void);
    	} else if(node instanceof KLabelConstant){
    		this.visit((KLabelConstant)node, _void);
    	} else if(node instanceof IntBuiltin){
    		this.visit((IntBuiltin)node, _void);
    	} else if(node instanceof StringBuiltin){
    		this.visit((StringBuiltin)node, _void);
    	} else if(node instanceof FloatBuiltin){
    		this.visit((FloatBuiltin)node, _void);
    	} else if(node instanceof BoolBuiltin){
    		this.visit((BoolBuiltin)node, _void);
    	}
    	return null;
    }
    
    public Void visit(ListTerminator terminator, Void _void) {
        System.out.print("[]");
        return null;
    }
    
    public Void visit(Variable variable, Void _void) {
        if (variable.isFreshVariable())
            System.out.print("?");
        else if (variable.isFreshConstant())
        	System.out.print("!");
        System.out.print(variable.getName());
        //System.out.print(":" + variable.getSort());
        return null;
    }
    
    public Void visit(Rewrite rewrite, Void _void) {
        this.visit(rewrite.getLeft(), _void);
        System.out.print(" ");
    	this.visit(rewrite.getRight(), _void);
    	return null;
    }
    
    public Void visit(Rule rule, Void _void) {
    	System.out.println("rule" + this.counter + ": \"");
    	this.counter++;
        if (rule.getRequires() != null) {
        	System.out.print(" ");
        	this.visit(rule.getRequires(), _void);
        	System.out.println("  \\<Longrightarrow> ");
        }
        if (rule.getEnsures() != null) {
        	System.out.print(" ");
        	this.visit(rule.getEnsures(), _void);
        	System.out.println("  \\<Longrightarrow> ");

        }
    	System.out.print(" impTheRule ");
        this.visit(rule.getBody(), _void);
        System.out.println("\"");
        return null;
    }
    
    public Void visit(Collection collection, Void _void) {
        java.util.List<Term> contents = collection.getContents();
        for (int i = 0; i < contents.size(); ++i) {
            this.visit(contents.get(i), _void);
        }
        if (contents.size() == 0) {
            System.out.print("[]");
        }
        return null;
    }
    
    public Void visit(Cell cell, Void _void) {
        System.out.print("(\"" + cell.getLabel()+"\", ");
        if (cell.hasLeftEllipsis()) {
            System.out.print(this.getGenVar()+"# ");
        }

        this.visit(cell.getContents(), _void);
        if (cell.hasRightEllipsis()) {
            System.out.print(" #"+this.getGenVar());
        }
        System.out.println(")");
        return null;
    }
    
    public Void visit(Bag bag, Void _void) {
        for (Term t : bag.getContents()) {
            this.visit(t, _void);
        }
        return null;
    }
    
    public Void visit(KApp kapp, Void _void) {
        this.visit(kapp.getLabel(), _void);
        if (!(kapp.getLabel() instanceof Token) && !(kapp.getLabel() instanceof KInjectedLabel)) {
            System.out.print(" ");
            this.visit(kapp.getChild(), _void);
            System.out.println(")");
        }
        return null;
    }
    
    public Void visit(KLabelConstant kLabelConstant, Void _void) {
        System.out.print(kLabelConstant.getLabel());
        return null;
    }
    
    public Void visit(KSequence ksequence, Void _void) {
        java.util.List<Term> contents = ksequence.getContents();
        System.out.print("(");
        if (!contents.isEmpty()) {
            for (int i = 0; i < contents.size(); i++) {
            	if(i == 0 && contents.get(i) instanceof KSequence){
            		if(((KSequence)contents.get(i)).getContents().isEmpty()){
            			System.out.print("[]");
            			break;
            		}
            	}
                this.visit(contents.get(i), _void);
                if (i != contents.size() - 1) {
                	System.out.print(" # ");
                }
            }
        } else {
        	System.out.print("[]");
        }
        System.out.println(")");
        return null;
    }
    
    public Void visit(ListBuiltin node, Void p) throws RuntimeException {
        for (Term t : node.elementsLeft()) {
            this.visit(t, p);
        }
        for (Term t : node.baseTerms()) {
            this.visit(t, p);
        }
        for (Term t : node.elementsRight()) {
            this.visit(t, p);
        }
        return null;
    }

    public Void visit(MapBuiltin node, Void p) throws RuntimeException {
        for (Map.Entry<Term, Term> entry : node.elements().entrySet()) {
            this.visit(entry.getKey(), p);
            this.visit(entry.getValue(), p);
        }
        for (Term t : node.baseTerms()) {
        	this.visit(t, p);
        }
        return null;
    }

    public Void visit(SetBuiltin node, Void p) throws RuntimeException {
        for (Term t : node.elements()) {
        	this.visit(t, p);
        }
        for (Term t : node.baseTerms()) {
        	this.visit(t, p);
        }
        return null;
    }
    
    public Void visit(IntBuiltin node, Void p) {
    	System.out.println(node.value());
        return null;
    }
    
    public Void visit(StringBuiltin node, Void p) {
    	System.out.println("\""+node.value()+"\"");
        return null;
    }
    
    public Void visit(FloatBuiltin node, Void p) {
    	System.out.println(node.value());
        return null;
    }
    
    public Void visit(BoolBuiltin node, Void p) {
    	if(node.value().equals(BoolBuiltin.TRUE)){
    		System.out.println("True");
    	} else {
    		System.out.println("False");
    	}
        return null;
    }
    
    public Void visit(TermCons termCons, Void _void) {
        Production production = termCons.getProduction();
        if (production.isListDecl()) {
            UserList userList = (UserList) production.getItems().get(0);
            String separator = "'_"+userList.getSeparator()+"_";
            java.util.List<Term> contents = termCons.getContents();
            System.out.print("("+separator+" ");
            this.visit(contents.get(0), _void);
            System.out.print(" ");
            this.visit(contents.get(1), _void);
            System.out.println(")");
        } else {
            int where = 0;
            String label = "'";
            ArrayList<Term> termList = new ArrayList<Term>();
            for (int i = 0; i < production.getItems().size(); ++i) {
                ProductionItem productionItem = (ProductionItem) production.getItems().get(i);
                if (!(productionItem instanceof Terminal)) {
                    Term subterm = (Term) termCons.getContents().get(where);
                    termList.add(subterm);
                    label += "_";
                    where++;
                } else {
                	label += ((Terminal) productionItem).getTerminal();
                }
            }
            System.out.print("("+label);
            for(int i = 0; i < termList.size(); ++i){
            	System.out.print(" ");
            	this.visit(termList.get(i), _void);
            }
            System.out.println(")");
        }
        return null;
    }
}
