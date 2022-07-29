/***** Parameters *****/

const margin = 20
const margin2 = 5



/***** Read file *****/

function loadJSONFile(filePath) {
  var result = null;
  var xmlhttp = new XMLHttpRequest();
  xmlhttp.open("GET", filePath, false);
  xmlhttp.send();
  if (xmlhttp.status==200) {
    result = JSON.parse(xmlhttp.responseText);
  } else {
    result = { "nodes": [], "layout": [] };
  }
  return result;
}



/***** Initialisation *****/

/* Create properties in each nodes which will be necessary later */
function formatData(json) {
  // Create a mapping from id to the node designated by the id
  const map = {};
  json.nodes.forEach(node => {
    map[node.id] = node;
  });
  // result will contain two fields
  const result = new Object();
  // result.nodes contains the nodes in a list of list representing the layout
  result.nodes = json.layout.map((nodes,lineNumber) => {
    return nodes.map((layoutNode, columnNumber) => {
      const node = map[layoutNode.id];
      node.color = Math.floor(Math.random() * 360);
      return node;
    });
  });
  // result.links contains the set of inequalities between nodes
  result.links = [];
  json.nodes.forEach(node => {
    node.children.forEach(childId => {
      result.links.push({"parent": node, "child": map[childId]})
    });
  });
  return result;
}



/***** Layout *****/

function computeNodeSize(domNode) {
  var width = 0;
  var height = 0;
  d3.select(domNode)
    .selectAll(".line")
    .each((d,i,nodes) => {
      const domLine = nodes[i];
      const domSpan = d3.select(domLine).select("span").node();
      lineWidth = domSpan.offsetWidth + 2*margin2;
      lineHeight = domSpan.offsetHeight + 2*margin2;
      size.set(domLine, {"width": lineWidth, "height": lineHeight});
      width = Math.max(width, lineWidth);
      height += lineHeight;
    });
  size.set(domNode, {"width": width, "height": height});
}

function applyLineSize(domLine, nodeWidth, currentHeight, delay) {
  const selection = d3.select(domLine);
  const lineHeight = size.get(domLine).height;
  selection
    .transition().duration(delay)
    .attr("transform", d => `translate(0,${currentHeight})`);
  selection.select("rect")
    .transition().duration(delay)
    .attr("width", nodeWidth)
    .attr("height", lineHeight);
  selection.select("foreignObject")
    .transition().duration(delay)
    .attr("width", nodeWidth)
    .attr("height", lineHeight);
}

function applyNodeSize(domNode, delay) {
  const nodeWidth = size.get(domNode).width;
  var currentHeight = 0;
  d3.select(domNode)
    .selectAll(".line")
    .each((d,i,nodes) => {
      const domLine = nodes[i];
      applyLineSize(domLine, nodeWidth, currentHeight, delay);
      currentHeight += size.get(domLine).height;
    });
}

function computeAllPositions(data) {
  var maxX = margin;
  var x = margin;
  var y = margin;
  data.nodes.forEach(line => {
    var nextY = y + margin;
    line.forEach(node => {
      domNode = d3.select("#" + node.id).node();
      position.set(domNode, {"x": x, "y": y});
      x += margin + size.get(domNode).width;
      nextY = Math.max(nextY, y + margin + size.get(domNode).height);
    });
    maxX = Math.max(maxX, x);
    x = margin;
    y = nextY;
  });
  maxY = y;
  domSVG = d3.select("svg").node();
  size.set(domSVG, {"width": maxX, "height": maxY});
}

function applySVGPosition(delay) {
  // Resize svg window
  domSVG = d3.select("svg").node();
  sizeSVG = size.get(domSVG);
  d3.select("svg")
    .transition().duration(delay)
    .attr("width", sizeSVG.width)
    .attr("height", sizeSVG.height);
}

function applyNodePosition(selection, delay) {
  selection
    .transition().duration(delay)
    .attr("transform", (d,i,nodes) => {
      domNode = nodes[i];
      positionNode = position.get(domNode);
      return `translate(${positionNode.x},${positionNode.y})`;
    });
}

function applyLinkPosition(selection, delay) {
  selection
    .transition().duration(delay)
    .attr("d", d => {
      domParent = d3.select("#" + d.parent.id).node();
      domChild = d3.select("#" + d.child.id).node();
      const pX = position.get(domParent).x + (size.get(domParent).width/2);
      const pY = position.get(domParent).y + size.get(domParent).height;
      const cX = position.get(domChild).x + (size.get(domChild).width/2);
      const cY = position.get(domChild).y;
      return `M ${pX} ${pY} C ${pX} ${cY}, ${cX} ${pY}, ${cX} ${cY}`
    });
}

function applyAllPositions(selectionNodes, selectionLinks, delay) {
  applySVGPosition(delay);
  applyNodePosition(selectionNodes, delay);
  applyLinkPosition(selectionLinks, delay);
}



/***** Plot *****/

function enterLine(selection, kind, mutable, text, partialClick) {
  /* Create a new <g> for each nodes */
  /* If the datum has a property [kind],
     then we fill the newly created <g> with the expected information. */
  addLineSelection = selection.filter(d => d.hasOwnProperty(kind))
    .append("g")
      .classed("line", true)
      .classed(kind, true)
    .each((d,i,nodes) => {
      if (mutable) {
        expand.set(nodes[i], false);
      }
    });
  rectSelection = addLineSelection.append("rect")
    .attr("x", 0)
    .attr("y", 0)
    .style("stroke", "black")
    .style("fill", "none");
  if (!mutable) {
    rectSelection.style("fill", d => "hsl(" + d.color + ", 50%, 90%)");
  }
  ForeignSelection = addLineSelection.append("foreignObject")
  if (mutable) {
    ForeignSelection.on("click", function(d) {
      domLine = this.parentNode;
      span = d3.select(this).select("span");
      if (expand.get(domLine)) {
          span.html(text);
      } else {
        span.html(d[kind]);
      }
      expand.set(domLine, !expand.get(domLine));
      computeNodeSize(domLine.parentNode);
      applyNodeSize(domLine.parentNode, 200);
      computeAllPositions(data);
      applyAllPositions(d3.selectAll(".node"), d3.selectAll(".link"), 200);
      return;
    })
  }
  ForeignSelection.append("xhtml:div") //TODO Ajouter la marge dans le js
    .append("xhtml:span")
    .html(d => mutable ? text : d[kind]);
}

function enterNode(selection) {
  result = selection.append("g")
    .classed("node", true)
    .attr("id", d => d.id);
  partialClick = null;
  enterLine(result, "name", false);
  enterLine(result, "cond", true, "Condition", partialClick);
  enterLine(result, "state", true, "States", partialClick);
  enterLine(result, "output", true, "Output", partialClick);
  result.each((d,i,node) => {
    const domNode = node[i];
    computeNodeSize(domNode);
    applyNodeSize(domNode, 0);
  });
  return result;
}

function enterLink(selection) {
  return selection.append("path")
    .classed("link", true)
    .attr("stroke", d => "hsl(" + d.parent.color + ", 100%, 50%)")
    .attr("stroke-width", "2")
    .attr("fill", "none");
}

function updateNode(selection) {
  return selection
}

function updateLink(selection) {
  return selection
}

/* Create elements corresponding to the initial data in the svg */
function plot(svg, data) {
  selectionNodes = svg.selectAll("g.node")
    .data(data.nodes.flat(), d => d.id)
    .join(
      enter => enterNode(enter),
      update => updateNode(update),
      exit => exit.remove()
    );

  selectionLinks = svg.selectAll("path")
    .data(data.links, d => d.parent.id + d.child.id)
    .join(
      enter => enterLink(enter),
      update => updateLink(update),
      exit => exit.remove()
    );

  svgSize = computeAllPositions(data);
  applySVGPosition(0);
  applyAllPositions(selectionNodes, selectionLinks, 0);
}




/***** Execution *****/

/**/
var size = d3.local();
var position = d3.local();
var expand = d3.local();
/* Declare the main svg */
d3.select("body")
  .append("xhtml:div");
var svg = d3.select("body")
  .append("svg")
  .style('border', 'solid')
var svgWidth;
var svgHeight;

/* Initialisation */
var json = loadJSONFile("http://localhost:8080/dump.json");
d3.select("div")
  .html(json.layout.flat().map(x => x.id).toString());
var data = formatData(json);

plot(svg, data);

/* Events */
const es = new EventSource('events');
es.addEventListener('update',
  function(event){
    json = loadJSONFile("http://localhost:8080/dump.json");
    var text = json.layout.flat().map(x => x.id).toString();
    d3.select("div")
      .html(text ? text : "No data");
    data = formatData(json);
    plot(svg, data);
  });
