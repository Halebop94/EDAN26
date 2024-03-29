import java.util.Iterator;
import java.util.ListIterator;
import java.util.LinkedList;
import java.util.BitSet;
import java.util.Collections;
import java.util.List;

class Random {
	int	w;
	int	z;

	public Random(int seed)
	{
		w = seed + 1;
		z = seed * seed + seed + 2;
	}

	int nextInt()
	{
		z = 36969 * (z & 65535) + (z >> 16);
		w = 18000 * (w & 65535) + (w >> 16);

		return (z << 16) + w;
	}
}

class Vertex {
	int			index;
	boolean			listed;
	LinkedList<Vertex>	pred;
	LinkedList<Vertex>	succ;
	BitSet			in;
	BitSet			out;
	BitSet			use;
	BitSet			def;

	Vertex(int i)
	{
		index	= i;
		pred	= new LinkedList<Vertex>();
		succ	= new LinkedList<Vertex>();
		in	= new BitSet();
		out	= new BitSet();
		use	= new BitSet();
		def	= new BitSet();
	}

	public synchronized void setListed(boolean listed) {
		this.listed = listed;
	}

	private synchronized void addIfNotPresent(List<Vertex> worklist) {
		if(!listed) {
			listed = true;
			worklist.add(this);
		}
	}

	void computeIn(List<Vertex> worklist)
	{
		succ.forEach(succVertex -> {
			synchronized(succVertex) {
				out.or(succVertex.in);
			}
		});


	BitSet old = in;

	// in = use U (out-def)

	synchronized(this) {
		in = new BitSet();
		in.or(out);
		in.andNot(def);
		in.or(use);
	}

	if(!in.equals(old)){
		pred.forEach(predVertex -> predVertex.addIfNotPresent(worklist));
	}
}


	public void print()
	{
		int	i;

		System.out.print("use[" + index + "] = { ");
		for (i = 0; i < use.size(); ++i)
			if (use.get(i))
				System.out.print("" + i + " ");
		System.out.println("}");
		System.out.print("def[" + index + "] = { ");
		for (i = 0; i < def.size(); ++i)
			if (def.get(i))
				System.out.print("" + i + " ");
		System.out.println("}\n");

		System.out.print("in[" + index + "] = { ");
		for (i = 0; i < in.size(); ++i)
			if (in.get(i))
				System.out.print("" + i + " ");
		System.out.println("}");

		System.out.print("out[" + index + "] = { ");
		for (i = 0; i < out.size(); ++i)
			if (out.get(i))
				System.out.print("" + i + " ");
		System.out.println("}\n");
	}

}

class WThread extends Thread {
	private List<Vertex> list;
	public int counter = 0;

	public WThread(List<Vertex> list){
		this.list = list;
	}

	@Override
	public void run() {
		while(!list.isEmpty()) {
			Vertex u = null;
			try{
				u = list.remove(0);
			} catch (IndexOutOfBoundsException e) {}
			if(u != null) {
				u.setListed(false);
				u.computeIn(list);
				counter++;
			}
		}
	}
}

class Dataflow {

	public static void connect(Vertex pred, Vertex succ)
	{
		pred.succ.addLast(succ);
		succ.pred.addLast(pred);
	}

	public static void generateCFG(Vertex vertex[], int maxsucc, Random r)
	{
		int	i;
		int	j;
		int	k;
		int	s;	// number of successors of a vertex.

		System.out.println("generating CFG...");

		connect(vertex[0], vertex[1]);
		connect(vertex[0], vertex[2]);

		for (i = 2; i < vertex.length; ++i) {
			s = (r.nextInt() % maxsucc) + 1;
			for (j = 0; j < s; ++j) {
				k = Math.abs(r.nextInt()) % vertex.length;
				connect(vertex[i], vertex[k]);
			}
		}
	}

	public static void generateUseDef(
		Vertex	vertex[],
		int	nsym,
		int	nactive,
		Random	r)
	{
		int	i;
		int	j;
		int	sym;

		System.out.println("generating usedefs...");

		for (i = 0; i < vertex.length; ++i) {
			for (j = 0; j < nactive; ++j) {
				sym = Math.abs(r.nextInt()) % nsym;

				if (j % 4 != 0) {
					if (!vertex[i].def.get(sym))
						vertex[i].use.set(sym);
				} else {
					if (!vertex[i].use.get(sym))
						vertex[i].def.set(sym);
				}
			}
		}
	}

	public static void liveness(Vertex vertex[], int nthread)
	{
		Vertex			u;
		Vertex			v;
		int			i;
		List<Vertex>	worklist;
		long			begin;
		long			end;

		System.out.println("computing liveness...");

		begin = System.nanoTime();
		worklist = Collections.synchronizedList(new LinkedList<Vertex>());

		for (i = 0; i < vertex.length; ++i) {
			worklist.add(vertex[i]);
			vertex[i].listed = true;
		}

		List<WThread> workerThreads = new LinkedList<WThread>();

		for(int j = 0; j < nthread; j++){
			WThread thread = new WThread(worklist);
			thread.start();
			workerThreads.add(thread);
		}

		workerThreads.forEach(t -> {
			try{
				t.join();
			} catch (Exception e) {

			}
		});

		end = System.nanoTime();

		System.out.println("T = " + (end-begin)/1e9 + " s");

		for(int k = 1; k < nthread+1; k++){
			System.out.println("Threadcounter " + k + ": " + workerThreads.get(k-1).counter);
		}
	}

	public static void sequential(Vertex vertex[]) {
		Vertex			u;
		Vertex			v;
		int			i;
		LinkedList<Vertex>	worklist;
		long			begin;
		long			end;

		System.out.println("computing liveness...");

		begin = System.nanoTime();
		worklist = new LinkedList<Vertex>();

		for (i = 0; i < vertex.length; ++i) {
			worklist.addLast(vertex[i]);
			vertex[i].listed = true;
		}

		while (!worklist.isEmpty()) {
			u = worklist.remove();
			u.listed = false;
			u.computeIn(worklist);
		}
		end = System.nanoTime();

		System.out.println("T = " + (end-begin)/1e9 + " s");
	}

	public static void main(String[] args)
	{
		int	i;
		int	nsym;
		int	nvertex;
		int	maxsucc;
		int	nactive;
		int	nthread;
		boolean	print;
		Vertex	vertex[];
		Random	r;

		r = new Random(1);

		nsym = Integer.parseInt(args[0]);
		nvertex = Integer.parseInt(args[1]);
		maxsucc = Integer.parseInt(args[2]);
		nactive = Integer.parseInt(args[3]);
		nthread = Integer.parseInt(args[4]);
		print = Integer.parseInt(args[5]) != 0;

		System.out.println("nsym = " + nsym);
		System.out.println("nvertex = " + nvertex);
		System.out.println("maxsucc = " + maxsucc);
		System.out.println("nactive = " + nactive);

		vertex = new Vertex[nvertex];

		for (i = 0; i < vertex.length; ++i)
			vertex[i] = new Vertex(i);

		generateCFG(vertex, maxsucc, r);
		generateUseDef(vertex, nsym, nactive, r);
		if(nvertex>=100){
			liveness(vertex, nthread);
		}
		else{
			sequential(vertex);
		}

		if (print)
			for (i = 0; i < vertex.length; ++i)
				vertex[i].print();
	}
}
