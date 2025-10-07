

method pick<T>(S:set<T>) returns (r:T)
  requires S != {} //&& |S| > 0
  ensures r in S
{
  var v :| v in S;
  return v;
}