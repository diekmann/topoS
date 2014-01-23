import networkx as nx

G = nx.read_gml('internet_routers-22july06.gml')
out = open('internet_routers-22july06.json', 'w')

print "num nodes: %d  num edges: %d" % (len(G.nodes()), len(G.edges()))


out.write( """{
"nodes": [
""" )

for n in G.nodes():
    out.write( """  "%s",\n""" % (n) )

out.write( "],\n""" )
out.write( """"edges": [
""" )

for (n1,n2) in G.edges():
    out.write( """  {"e1": "%s", "e2": "%s"},\n""" % (n1, n2) )

out.write( """ ]
}
""" )
