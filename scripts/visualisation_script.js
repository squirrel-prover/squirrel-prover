/* [data] is declared in another file 
   Data is an array of levels, and levels are non-empty array of nodes*/

const margin = 20



/***** Initialisation *****/

/* Create properties in each nodes which will be necessary later */
function make_data(json) {
  const dic = {};
  json.nodes.forEach(node => {
    dic[node.id] = node;
  });
  const data = [];
  json.layout.forEach(level => {
    console.log(level);
    const dataLevel = [];
    level.forEach(nodeId => {
      const node = dic[nodeId.id];
      node.level = dataLevel;
      node.lineWidth = {};
      node.lineHeight = {};
      node.lineDisplay = {};
      dataLevel.push(node);
    });
    data.push(dataLevel);
  });
  const links = [];
  json.nodes.forEach(node => {
    node.children.forEach(child => {
      links.push({"parent": node, "child": dic[child]})
    });
  });
  return [data, links]
}

  

/***** Layout *****/

/* Compute height, width, x and y of nodes and levels in data
   Use heights and widths of each sub-elements inside nodes
   (i.e. values inside properties lineHeight and lineWidth). */
function computePositions(data) {
  svgWidth = margin;
  svgHeight = margin;
  data.forEach((level,i,levels) => {
    level.width = margin;
    level.height = 0;
    level.forEach((node,j,nodes) => {
      node.width = Math.max(...Object.values(node.lineWidth));
      node.height = Object.values(node.lineHeight).reduce((x,y) => x+y, 0);
      node.x = j > 0 ? (nodes[j-1].x + nodes[j-1].width + margin) : margin;
      node.y = 0;
      node.level.width += node.width + margin;
      node.level.height = Math.max(node.level.height, node.height);
    });
    level.x = 0;
    level.y = i > 0 ? (levels[i-1].y + levels[i-1].height + margin) : margin;
    svgWidth = Math.max(svgWidth, level.width);
    svgHeight += level.height + margin;
  });
}

/* Upadte position of DOM element corresponding to a line inside a node */
function updateLine(selection, kind, previousKind, delay) {
  selectionNodes.select("g." + kind)
    .transition().duration(delay)
    .attr("transform", d => `translate(0,${previousKind ? d.lineHeight[previousKind] : 0})`);
  selectionNodes.select("rect." + kind)
    .transition().duration(delay)
    .attr("width", d => d.width)
    .attr("height", d => d.lineHeight[kind]);
  selectionNodes.select("foreignObject." + kind)
    .transition().duration(delay)
    .attr("width", d => d.width)
    .attr("height", d => d.lineHeight[kind]);
}

/* Update positions of each element in the SVG */
function updateAll(selectionLevels, selectionNodes, selectionLinks, delay) {
  // Resize svg window
  d3.select("svg")
    .transition().duration(delay)
    .attr("width", svgWidth)
    .attr("height", svgHeight)
  // Place levels, nodes, and links
  selectionLevels
    .transition().duration(delay)
    .attr("transform", d => `translate(${d.x},${d.y})`);
  selectionNodes
    .transition().duration(delay)
    .attr("x", d => d.x)
    .attr("y", d => d.y)
    .attr("transform", d => `translate(${d.x},${d.y})`);
  selectionLinks
    .transition().duration(delay)
    .attr("d", d => {
      const pX = d.parent.x + (d.parent.width/2);
      const pY = d.parent.level.y + d.parent.y + d.parent.height;
      const cX = d.child.x + (d.child.width/2);
      const cY = d.child.y + d.child.level.y;
      return `M ${pX} ${pY} C ${pX} ${cY}, ${cX} ${pY}, ${cX} ${cY}`
    });
  // Use height and width to put all attributes for the differents part of a node
  updateLine(selectionNodes, "name", null, delay);
  updateLine(selectionNodes, "cond", "name", delay);
  updateLine(selectionNodes, "state", "cond", delay);
  updateLine(selectionNodes, "output", "state", delay);
}



/***** Interaction *****/

/* Expand or reduce the output line */
function click(data, selectionLevels, selectionNodes, selectionLinks, delay) {
  return function(d, element, kind, text) {
    span = d3.select(element).select("span");
    if (d.lineDisplay[kind]) {
      span.html(text);
    } else {
      span.html(d[kind]);
    }
    d.lineDisplay[kind] = !d.lineDisplay[kind];
    d.lineWidth[kind] = span.node().offsetWidth;
    d.lineHeight[kind] = span.node().offsetHeight;
    computePositions(data);
    updateAll(selectionLevels, selectionNodes, selectionLinks, delay);
  };
}



/***** Plot *****/

/* Add a sub-elements to each nodes in the SVG
   (if the nodes contains the property [kind]) */
function plot_line(selection, kind, mutable, text, partialClick) {
  /* Create a new <g> for each nodes */
  newSelection = selection
    .append("g")
    .attr("class", kind)
    .each(function(d) {
      d.lineWidth[kind] = 0;
      d.lineHeight[kind] = 0;
    });
  /* If the datum has a property [kind],
     then we fill the newly created <g> with the expected information. */
  validSelection = newSelection.filter(d => d.hasOwnProperty(kind));
  validSelection.append("rect")
    .classed(kind, true)
    .attr("x", 0)
    .attr("y", 0)
    .style("fill", "none")
    .style("stroke", "black");
  FOSelection = validSelection.append("foreignObject")
    .classed(kind, true);
  if (mutable) {
    FOSelection.on("click", function(d) {
      partialClick(d, this, kind, text);
      updateAll(selectionLevels, selectionNodes, selectionLinks, 500);
    })
  }
  FOSelection.append("xhtml:span")
      .html(d => mutable ? text : d[kind])
      .each(function(d) {
        d.lineWidth[kind] = this.offsetWidth;
        d.lineHeight[kind] = this.offsetHeight;
      });
  /* We return the created selection. */
  return newSelection
}

/* Create elements corresponding to the initial data in the svg */
function plot(data, links, svg) {
  // First we crete all the selections.
  // This will crete groups in the DOM of the SVG.
  // The selection will link these groups to data.
  // SelectionLevel connect levels to an element <g> which will contain element of a line of nodes
  selectionLevels = svg.selectAll("g")
    .data(data)
    .enter()
    .append("g")
      .attr("id", (d,i) => `lvl${i}`);
  // SelectionNodes connect nodes to an element <g> which will contain element of the node
  selectionNodes = selectionLevels.selectAll("g")
    .data(function(d) { return d; })
    .enter()
    .append("g")
      .attr("class", "node")
      .attr("id", d => d.id);
  // SelectionLinks connect links to elements <path>
  selectionLinks = svg.selectAll("path")
    .data(links)
    .enter()
    .append("path")
      .attr("stroke", "red")
      .attr("stroke-width", "2")
      .attr("fill", "none");
  
  // Create all the elements inside a node
  partialClick = click(data, selectionLevels, selectionNodes, selectionLinks, 2000)
  selectionName = plot_line(selectionNodes, "name", false);
  selectionCond = plot_line(selectionName, "cond", true, "Condition", partialClick);
  selectionState = plot_line(selectionCond, "state", true, "States", partialClick);
  selectionOutput = plot_line(selectionState, "output", true, "Output", partialClick);
  
  // Since textual element are created in <foreignObject>,
  // we can now compute height and width of each nodes
  // and x of each nodes and y of each levels
  computePositions(data);
  
  // Use height and width to put all attributes for the differents part of a node
  updateAll(selectionLevels, selectionNodes, selectionLinks, 0);
}



/***** Execution *****/

/* Declare the main svg */
var svg = d3.select("body")
  .append("svg")
  .style('background-color', 'lightgrey')
/* Initialisation */
const [data, links] = make_data(json);
console.log(data);
console.log(links);
/* Plot */
plot(data, links, svg);
