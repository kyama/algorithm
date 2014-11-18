
/**
 * RESULT
 * using ZDD.java
 * n= 3 result:true time:44(ms) ans:12
 * n= 4 result:true time:147(ms) ans:184
 * n= 5 result:true time:214(ms) ans:8512
 * n= 6 result:true time:416(ms) ans:1262816
 * n= 7 result:true time:939(ms) ans:575780564
 * n= 8 result:true time:1512(ms) ans:789360053252
 * n= 9 result:true time:22308(ms) ans:3266598486981642
 * 
 * not using ZDD.java
 * n= 3 result:true time:42(ms) ans:12
 * n= 4 result:true time:162(ms) ans:184
 * n= 5 result:true time:202(ms) ans:8512
 * n= 6 result:true time:247(ms) ans:1262816
 * n= 7 result:true time:600(ms) ans:575780564
 * n= 8 result:true time:1610(ms) ans:789360053252
 * n= 9 result:true time:4536(ms) ans:3266598486981642
 * 
 * using BigInteger because it is not enough for long to answer for more than or eqauls to 10 x 10 vertices.
 * n= 3 result:true time:40(ms) ans:12
 * n= 4 result:true time:151(ms) ans:184
 * n= 5 result:true time:174(ms) ans:8512
 * n= 6 result:true time:250(ms) ans:1262816
 * n= 7 result:true time:667(ms) ans:575780564
 * n= 8 result:true time:1494(ms) ans:789360053252
 * n= 9 result:true time:4785(ms) ans:3266598486981642
 * n=10 result:true time:16989(ms) ans:41044208702632496804
 * n=11 result:true time:57301(ms) ans:1568758030464750013214100
 *
 * mbpro
 * n= 3 result:true time:7(ms) ans:12
 * n= 4 result:true time:10(ms) ans:184
 * n= 5 result:true time:29(ms) ans:8512
 * n= 6 result:true time:54(ms) ans:1262816
 * n= 7 result:true time:246(ms) ans:575780564
 * n= 8 result:true time:826(ms) ans:789360053252
 * n= 9 result:true time:1401(ms) ans:3266598486981642
 * n=10 result:true time:5279(ms) ans:41044208702632496804
 * n=11 result:true time:20609(ms) ans:1568758030464750013214100
 * n=12 result:true time:142800(ms) ans:182413291514248049241470885236
 *
 * @refer http://www-cs-faculty.stanford.edu/~uno/programs.html -- Prof.Don Knuth's original simpath
 * @refer http://oeis.org/A007764 -- the answers
 **/
import static java.lang.Math.*;
import java.util.*;
import java.math.BigInteger;
public class Simpath{
    int N;
    boolean edgePrintFlg=false;
    boolean matePrintFlg=false;
    boolean nodePrintFlg=false;
    Map<Node,Long> cnt;
    Map<Node,BigInteger> cntbi;
    StringBuffer nodeOutput;
    StringBuffer mateOutput;
    int[] hashPrePro;

    static String[] Ans;
    static {
	Ans = new String[13];
	Ans[2] = "2";
	Ans[3] = "12";
	Ans[4] = "184";
	Ans[5] = "8512";
	Ans[6] = "1262816";
	Ans[7] = "575780564";
	Ans[8] = "789360053252";
	Ans[9] = "3266598486981642";
	Ans[10]= "41044208702632496804";
	Ans[11]= "1568758030464750013214100";
	Ans[12]= "182413291514248049241470885236";
    }

    Edge NullEdge = new Edge();
    class Edge{
	int v,st,ed;
	Edge(){ v=-1;st=0;ed=0; }
	Edge(int n,int s,int e){ v=n; st=s; ed=e; }
	boolean isNull(){ return this==NullEdge; }
    }
    Node True  = new Node(-1);
    Node False = new Node(-2);
    class Node{
	Node lo=False,hi=False;
	int val;
	Node(int v){val=v;}
    }
    public void init(){
	cnt   = new HashMap<Node,Long>();
	cntbi = new HashMap<Node,BigInteger>();
	nodeOutput = new StringBuffer();
	mateOutput = new StringBuffer();
    }
    public String solve(int n){
	init();
	N = n*n; // number of vertices

	// preprocess for calculating hashCode
	hashPrePro = new int[N+2];
	hashPrePro[0]=1;
	for(int i=0;i<=N;i++) hashPrePro[i+1] = (N+1) * hashPrePro[i];

	// create edges
	Edge[] edge = new Edge[2*(n-1)*n+1];
	edge[0] = NullEdge;
	for(int y=0,i=1,j=1;y<n;y++){ 
	    for(int x=0;x<n;x++){
		if(y+1<n) edge[i] = new Edge(i++,j,j+n);
		if(x+1<n) edge[i] = new Edge(i++,j,j+1);
		j++;
	    }
	}

	// print edges
	if(edgePrintFlg)
	    for(Edge e:edge){
		if(e.v<1) continue;
		if(e.st>=N) break;
		System.out.printf("%2d (%2d -> %2d)\n",e.v,e.st,e.ed);
	    }

	//
	// initialize
	//
	Map<Integer,Node>    ztable = new HashMap<Integer,Node>();
	Map<Integer,int[]>   htable = new HashMap<Integer,int[]>();
	Set<Integer>       nextmate = new LinkedHashSet<Integer>();
	Map<Integer,Integer> ctable = new HashMap<Integer,Integer>();
	// zdd
	Node result = new Node(1);
	// frontier
	int nst=1,ned=1; // next start and end of frontier

	// mate
	int[] mate = new int[N+1];
	for(int i=1;i<=N;i++) mate[i] = i;
	mate[1] = N;
	mate[N] = 1;

	int counter=2;
	int hash = hashCode(mate,nst,ned);
	nextmate.add(hash);
	htable.put(hash,Arrays.copyOfRange(mate,nst,ned+1));
	ztable.put(hash,result);
	ctable.put(hash,counter);


	//
	// solve the problem
	//
	for(int i=1;i<edge.length;i++){
	    if(edge[i].ed>N) break;
	    addNodes("#%d:\n",i);
	    int fst=nst, fed=ned; // copy next frontier to current frontier of start and end
	    int ked=edge[i].ed;
	    ned = max(fed,edge[i].ed);

	    if(i+1<edge.length) nst = edge[i+1].st; else nst++;

	    Set<Integer> nextmate2 = new LinkedHashSet<Integer>(nextmate); 
	    nextmate.clear();
	    Iterator<Integer> ite = nextmate2.iterator();
	    while(ite.hasNext()){
		hash = ite.next();
		int[] m = htable.get(hash);
		for(int t=fst;t<=fed;t++){
		    mate[t] = m[t-fst];
		    if(mate[t]>fed) mate[mate[t]]=t;
		}
		addNodes("%x:",ctable.get(hash));
		if(matePrintFlg){
		    String log1 = String.format("%s",Arrays.toString(m));
		    String log2 = String.format("i:%d j:%d jj:%d k:%d l:%d ll:%d hash:%d",
						edge[i].v, fst, nst,  ked, fed, ned,  hash);
		    addMate("%s\t\t\t%s\n",log1,log2);
		}
		int t;
		//
		// not choose i-th edge
		//
		if((t=checkState(mate,fst,nst,ned))>0){

		    if(t<nst || ned<nst){
			ztable.get(hash).lo = False;
			addNodes("\t0,");
		    }else{
			int next_hash = hashCode(mate,nst,ned);
			int[] nmate = Arrays.copyOfRange(mate,nst,ned+1);
			while(htable.containsKey(next_hash) && ! Arrays.equals(htable.get(next_hash), nmate)) next_hash++;
			nextmate.add(next_hash);

			if( ! ctable.containsKey(next_hash)) ctable.put(next_hash,++counter);
			addNodes("\t%x,",ctable.get(next_hash));

			// mate
			if( ! htable.containsKey(next_hash)) htable.put(next_hash,nmate);
			if( ! ztable.containsKey(next_hash)) ztable.put(next_hash,new Node(i+1));
			ztable.get(hash).lo = ztable.get(next_hash);
		    }
		}else{
		    ztable.get(hash).lo = False;
		    addNodes("\t0,");
		}
		
		//
		// choose i-th edge
		//
		int mst = mate[fst];
		int med = mate[ked];
		if(mst==0 || med==0){
		    // ZDD:Eliminate all the nodes whose 1-edge points to the 0-terminal node.
		    addNodes("0");
		}else if(mst==ked){
		    for(t=fst+1;t<=ned;t++)
			if(t!=ked && mate[t]!=0 && mate[t]!=t) break;
		    
		    if(t>ned){
			ztable.get(hash).hi=True;
			addNodes("1");
		    }else{
			// ZDD:Eliminate all the nodes whose 1-edge points to the 0-terminal node.
			addNodes("0");
		    }
		}else{
		    mate[fst] = 0;
		    mate[ked] = 0;
		    mate[mst] = med;
		    mate[med] = mst;
		    if((t=checkState(mate,fst,nst,ned))>0){
			
			if(t<nst || ned<nst){
			    // ZDD:Eliminate all the nodes whose 1-edge points to the 0-terminal node.
			    addNodes("0");
			}else{
			    int next_hash = hashCode(mate,nst,ned);
			    int[] nmate = Arrays.copyOfRange(mate,nst,ned+1);
			    while(htable.containsKey(next_hash) && ! Arrays.equals(htable.get(next_hash),nmate)) next_hash++;
			    nextmate.add(next_hash);

			    if( ! ctable.containsKey(next_hash)) ctable.put(next_hash,++counter);
			    addNodes("%x",ctable.get(next_hash));

			    // mate
			    if( ! htable.containsKey(next_hash)) htable.put(next_hash,nmate);
			    if( ! ztable.containsKey(next_hash)) ztable.put(next_hash,new Node(i+1));
			    ztable.get(hash).hi = ztable.get(next_hash);
			}
		    }else{
			// ZDD:Eliminate all the nodes whose 1-edge points to the 0-terminal node.
			addNodes("0");
		    }
		    // restore original state
		    mate[mst] = fst;
		    mate[med] = ked;
		    mate[fst] = mst;
		    mate[ked] = med;
		}
		addNodes("\n");
	    }
	}
	
	printNodes();
	printMate();
	long r = count(result);
	BigInteger numOfRoutes = countBI(result);
	System.err.printf("%d\n",numOfRoutes);
	//System.err.printf("%d\n",r);
	System.err.printf("counter:%x(16) %d(10)\n",counter,counter);
	return numOfRoutes.toString();
    }
    public int checkState(int[] m, int fst,int nst,int ned){
	int t;
	for(t=fst;t<nst;t++) if(m[t]!=0 && m[t]!=t) break;

	if(t<nst || ned<nst) return -1;
	return t;
    }
    public int hashCode(int[] m,int st,int ed){
	int hash = hashPrePro[st-1];
	
	for(int i=st;i<=ed;i++) hash = hash*(N+2) + m[i];
	hash += hashPrePro[N]-hashPrePro[ed];
	
	return hash;
    }
    public long count(Node n){
	if(n==True)  return 1L;
	if(n==False) return 0L;
	if(cnt.containsKey(n)) return cnt.get(n);
	cnt.put(n,count(n.hi)+count(n.lo));
	return cnt.get(n);
    }

    public BigInteger countBI(Node n){
	if(n==True)  return BigInteger.ONE;
	if(n==False) return BigInteger.ZERO;;
	if(cntbi.containsKey(n)) return cntbi.get(n);
	cntbi.put(n,countBI(n.hi).add(countBI(n.lo)));
	return cntbi.get(n);
    }
    public void addNodes(String str,Object...options){
	if( ! nodePrintFlg) return;
	nodeOutput.append(String.format(str,options));
    }
    public void printNodes(){
	if( ! nodePrintFlg) return;
	System.out.println(nodeOutput);
    }
    public void addMate(String str,Object...options){
	if( ! matePrintFlg) return;
	mateOutput.append(String.format(str,options));
    }
    public void printMate(){
	if( ! matePrintFlg) return;
	System.out.println(mateOutput);
    }
    //
    // main 
    //
    public static void main(String[] argv){
	int default_st=3, default_ed=10;
	if(argv.length>0){
	    Simpath simpath = new Simpath();
	    int n=-1;
	    for(int i=0;i<argv.length;i++){
		if(argv[i].charAt(0)=='-'){
		    switch(argv[i].charAt(1)){
		    case 'h' : StringBuffer out = new StringBuffer();
			out.append(String.format("java Simpath [options]\n"));
			out.append(String.format("\t-h print this help message\n"));
			out.append(String.format("\t-n <number n> n x n grid\n"));
			out.append(String.format("\t-p [edge|mate|node]\n"));
			out.append(String.format("\t   edge -- print edges\n"));
			out.append(String.format("\t   mate -- print mate\n"));
			out.append(String.format("\t   node -- print nodes. it's the same output as prof.Don Knuth's simpath gives\n"));
			System.out.println(out);
			System.exit(0);
			break;
		    case 'p' : 
			i++;
			if(argv[i].equals("edge")) simpath.edgePrintFlg=true;
			if(argv[i].equals("mate")) simpath.matePrintFlg=true;
			if(argv[i].equals("node")) simpath.nodePrintFlg=true;
			break;
		    case 'n' : 
			n=Integer.parseInt(argv[++i]);
			break;
		    }
		}
	    }
	    if(n>0) simpath.solve(n);
	    else    test(simpath,default_st,default_ed);
	}else{
	    test(new Simpath(),default_st,default_ed);
	}
    }
    public static void test(Simpath sp,int fr,int to){
	long[] time = new long[to+1];
	boolean[] results = new boolean[to+1];
	for(int i=fr;i<=to;i++){
	    long st = System.currentTimeMillis();
	    results[i] = check(sp,i,Ans[i]);
	    time[i] = System.currentTimeMillis()-st;
	}
	for(int i=fr;i<=to;i++){
	    System.out.printf("n=%2d result:%s time:%d(ms) ans:%s\n",
			      i,results[i],time[i],Ans[i]);
	}
    }
    public static boolean check(Simpath sp,int n,String exp){
	//	String ans  = new Simpath().solve(n);
	String ans = sp.solve(n);
	return ans.equals(exp);
    }
}
