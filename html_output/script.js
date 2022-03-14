lines = document.querySelectorAll("span.squirrel-step");
outputLines = document.querySelectorAll("span.output-line");
inputLines = document.querySelectorAll("span.input-line");
inLine = document.getElementById("in-line");
outLine = document.getElementById("out-line");
precLine = document.getElementById("prec-line");

stepBegin = []
stepEnd = []
i = 0;
n = lines.length;
panel = false;

function init() {
  for (j = 0; j < n; j++) {
    line = lines[j];

    input = line.getElementsByClassName("input-line")[0];
    input.ondblclick = function(){gotoLine(this.number+1);};
    input.number = j;
    
    comContent = line.getElementsByClassName("com-line");
    if (comContent.length > 0) {
      com = document.createElement('div');
      com.className = 'comment';
      com.innerHTML = comContent[0].innerHTML;
      com.collapse = false;
      com.text = com.innerHTML;
      com.addEventListener("dblclick", function() { collapseBox(this); } );
      inLine.appendChild(com);
      stepBegin.push(com);
    } else {
      stepBegin.push(input);
    }
    stepEnd.push(input);
    
    inLine.appendChild(input);
  }
}

function goView(j, stepVector) {
  options = {behavior: "smooth", block: "nearest", inline: "nearest"}
  if (j <= 1) {
    stepVector[0].scrollIntoView(options);
  } else {
    stepVector[j-1].scrollIntoView(options);
  }
}

function gotoLine(j) {
  if (0 <= j && j <= n){
    if (j <= 1){
      precLine.innerHTML = ""; 
    } else {
      precLine.innerHTML = outputLines[j-2].innerHTML;
    }
    if (j == 0){
      outLine.innerHTML = ""; 
    } else {
      outLine.innerHTML = outputLines[j-1].innerHTML;
    }
    for (k = 0; k < j; k++) {
      inputLines[k].style.background = "#cfdbeb";
    }
    for (k = j; k < n; k++) {
      inputLines[k].style.background = "none";
    }
    i = j;
  }
}

function gotoUp() {
  gotoLine(i+1);
  goView(i, stepEnd);
}

function gotoDown() {
  gotoLine(i-1);
  goView(i, stepBegin);
}

function key(event) {
  x = event.key;
  if (x == "ArrowRight") { gotoUp() }
  else if (x == "ArrowLeft") { gotoDown() }
}

function help() {
  if (panel) {
    document.getElementById("help-panel").style.width = "0";
    document.getElementById("help-panel").style.padding = "3.5rem 0 0.5rem";
    document.getElementById("main").style.width = "100%";
    panel = false;
  } else {
    document.getElementById("help-panel").style.width = "20%";
    document.getElementById("help-panel").style.padding = "3.5rem 0.5rem 0.5rem";
    document.getElementById("main").style.width = "80%";
    panel = true;
  }
}

function collapseBox(obj) {
  obj.classList.toggle("collapsed");
   "+ ---------------";
  
  if (obj.collapse) {
    obj.innerHTML = obj.text;
    obj.collapse = false;
  } else {
    obj.innerHTML = "+ ---------------";
    obj.collapse = true;
  }
}

function highlightOn(id) {
  document.getElementById(id).style.backgroundColor = "#ffff9b";
}

function highlightOff(id) {
  document.getElementById(id).style.backgroundColor = "white";
}

function hidePrec() {
  
  button = document.getElementById('prec-button');
  if (button.status) {
    document.getElementById('out-zone').style.height = "55%";
    document.getElementById('prec-zone').style.display = "block";
    button.innerHTML = "Hide";
    button.status = false;
  } else {
    document.getElementById('out-zone').style.height = "100%";
    document.getElementById('prec-zone').style.display = "none";
    button.innerHTML = "Show";
    button.status = true;
  }
  
}

init()
