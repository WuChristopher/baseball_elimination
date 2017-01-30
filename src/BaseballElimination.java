import edu.princeton.cs.algs4.*;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;

/**
 * Created by Christopher on 28/01/2017.
 */

/**
 * This is all about using maxflow problem solving model to tackle the baseball elimination
 * problem, the key is to construct the flow network based on the lecture slides and the
 * assignment specification. My implementation caches the historical queries' results for
 * future use. In order to iterate the hash map in a determined order, the LinkedHashMap is
 * used, because in the real world, the size of the problem is often tiny, so we don't care
 * about losing some efficiency in using LinkedHashMap instead of HashMap.
 */
final public class BaseballElimination {

    private final LinkedHashMap<String, Integer> teams; // team and associated ID
    private final HashMap<Integer, String> ids; // map id to team name
    private final int[] wins;
    private final int[] losses;
    private final int[] remaining;
    private final int[][] against;
    private final int currentLead; // id of the current lead team
    private HashMap<String, LinkedHashSet<String>> certOfElimination;

    public BaseballElimination(String filename) {
        if (filename == null) throw new NullPointerException();
        int num;
        String line;
        In in = new In(filename);
        if (in.hasNextLine()) {
            line = in.readLine();
            num = Integer.parseInt(line);
        } else throw new IllegalArgumentException("team number not found");
        teams = new LinkedHashMap<>();
        ids = new HashMap<>();
        wins = new int[num];
        losses = new int[num];
        remaining = new int[num];
        against = new int[num][num];
        certOfElimination = new HashMap<>();

        int cnt = 0;
        while (in.hasNextLine()) {
            line = in.readLine();
            line = line.trim(); // remove any leading and trailing spaces
            String[] fields = line.split("\\s+"); // note the regex used here
            teams.put(fields[0], cnt);
            ids.put(cnt, fields[0]);
            wins[cnt] = Integer.parseInt(fields[1]);
            losses[cnt] = Integer.parseInt(fields[2]);
            remaining[cnt] = Integer.parseInt(fields[3]);
            for (int i = 0; i < num; i++) {
                against[cnt][i] = Integer.parseInt(fields[4 + i]);
            }
            // increment the sequential ID of the current team
            cnt++;
        }
        currentLead = max(wins);
    }

    public int numberOfTeams() { return teams.size(); }

    /**
     * Always return a determined order of collection teams.
     */
    public Iterable<String> teams() {
        return teams.keySet();
    }

    public int wins(String team) {
        if (team == null) throw new NullPointerException();
        if (!teams.containsKey(team)) throw new IllegalArgumentException("no team " + team);
        int id = teams.get(team);
        return wins[id];
    }

    public int losses(String team) {
        if (team == null) throw new NullPointerException();
        if (!teams.containsKey(team)) throw new IllegalArgumentException("no team " + team);
        int id = teams.get(team);
        return losses[id];
    }

    public int remaining(String team) {
        if (team == null) throw new NullPointerException();
        if (!teams.containsKey(team)) throw new IllegalArgumentException("no team " + team);
        int id = teams.get(team);
        return remaining[id];
    }

    public int against(String team1, String team2) {
        if (team1 == null || team2 == null) throw new NullPointerException();
        if (!teams.containsKey(team1)) throw new IllegalArgumentException("no team " + team1);
        if (!teams.containsKey(team2)) throw new IllegalArgumentException("no team " + team2);
        int id1 = teams.get(team1);
        int id2 = teams.get(team2);
        return against[id1][id2];
    }

    public boolean isEliminated(String team) {
        // input sanity check
        if (team == null) throw new NullPointerException();
        if (!teams.containsKey(team)) throw new IllegalArgumentException("no team " + team);
        if (certOfElimination.containsKey(team)) {
            HashSet<String> cert = certOfElimination.get(team);
            if (cert != null) return true;
            else return false;
        } else {
            elimination(team);
            HashSet<String> cert = certOfElimination.get(team);
            if (cert != null) return true;
            else return false;
        }
    }

    public Iterable<String> certificateOfElimination(String team) {
        // input sanity check
        if (team == null) throw new NullPointerException();
        if (!teams.containsKey(team)) throw new IllegalArgumentException("no team " + team);
        if (certOfElimination.containsKey(team))
            return certOfElimination.get(team);
        else {
            elimination(team);
            return certOfElimination.get(team);
        }
    }

    /**
     * This method is the core of the solution. And the key of this method is to build
     * the flow network graph and add all the corresponded edges, note that the capacity
     * of edges from game vertices to team vertices are always positive infinity. In this
     * method, use a teamVertices array to store the team vertices number so as to determine
     * all the teams' vertex numbers by checking the team id, which is from 0 to num of teams
     * minus 1. In the elimination flow network, source vertex number is 0, and termination
     * vertex number is (num of vertices - 1). The numbers of games start from 1 and are
     * continuous, after which are the numbers of the teams. When all the vertices are there,
     * it is not difficult the construct the whole flow network.
     */
    private void elimination(String team) {
        if (team == null) throw new NullPointerException();

        int id = teams.get(team); // the queried team id
        if (wins[id] + remaining[id] < wins[currentLead]) {
            LinkedHashSet<String> hs = new LinkedHashSet<>();
            hs.add(ids.get(currentLead));
            certOfElimination.put(team, hs);
            return;
        }

        int num = teams.size();
        int gameVertices = (num - 1) * (num - 2) / 2;
        int fnVertices = 2 + gameVertices + (num - 1);
        FlowNetwork fn = new FlowNetwork(fnVertices);
        int[] teamVertices = new int[num];
        // determine the vertices number of the teams
        int cnt = gameVertices + 1;
        for (int i = 0; i < num; i++) {
            if (i == id) teamVertices[i] = -1;
            else teamVertices[i] = cnt++;
        }

        boolean[] marked = new boolean[num];
        // cnt now stands for the game vertices number
        cnt = 1;
        for (int i = 0; i < num; i++) {
            if (i == id) continue;
            for (int j = i + 1; j < num; j++) {
                if (j == id) continue;
                FlowEdge fe = new FlowEdge(0, cnt, against[i][j], 0.0);
                fn.addEdge(fe);
                fe = new FlowEdge(cnt, teamVertices[i], Double.POSITIVE_INFINITY, 0.0);
                fn.addEdge(fe);
                fe = new FlowEdge(cnt, teamVertices[j], Double.POSITIVE_INFINITY, 0.0);
                fn.addEdge(fe);
                // process edge of teams[i] to T vertex
                if (!marked[i]) {
                    fe = new FlowEdge(teamVertices[i], fnVertices - 1,
                            wins[id] + remaining[id] - wins[i], 0.0);
                    fn.addEdge(fe);
                    marked[i] = true;
                }
                // process edge of teams[j] to T vertex
                if (!marked[j]) {
                    fe = new FlowEdge(teamVertices[j], fnVertices - 1,
                            wins[id] + remaining[id] - wins[j], 0.0);
                    fn.addEdge(fe);
                    marked[j] = true;
                }
                // next loop deals with next game vertex
                cnt++;
            }
        }
        // the loops should have dealt with this gameVertices flow network vertices
        assert(cnt - 1 == gameVertices);
        // calculate the capacity of edges incident to Source vertex
        int cap = 0;
        for (FlowEdge e : fn.adj(0))
            cap += e.capacity();
        FordFulkerson ff = new FordFulkerson(fn, 0, fnVertices - 1);
        if (cap == ff.value()) certOfElimination.put(team, null);
        else {
            LinkedHashSet<String> hs = new LinkedHashSet<>();
            for (int i = 0; i < num; i++) {
                if (i == id) continue; // exclude the queried team
                if (ff.inCut(teamVertices[i])) hs.add(ids.get(i));
            }
            certOfElimination.put(team, hs);
        }

    }

    /**
     * Return the index of max value of the array entries
     */
    private int max(int[] arry) {
        int maxVal = Integer.MIN_VALUE;
        int idx = 0;
        for (int i = 0; i < arry.length; i++) {
            if (arry[i] > maxVal) {
                maxVal = arry[i];
                idx = i;
            }
        }
        return idx;
    }

    /**
     * For unit testing.
     */
    public static void main(String[] args) {
        BaseballElimination division = new BaseballElimination(args[0]);
        for (String team : division.teams()) {
            if (division.isEliminated(team)) {
                StdOut.print(team + " is eliminated by the subset R = { ");
                for (String t : division.certificateOfElimination(team)) {
                    StdOut.print(t + " ");
                }
                StdOut.println("}");
            }
            else {
                StdOut.println(team + " is not eliminated");
            }
        }
    }
}