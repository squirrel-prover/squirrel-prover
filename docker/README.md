# Running docker

After installing Docker (https://docs.docker.com/engine/install/), the docker image with squirrel preinstalled can be obtained with

$ docker pull cjacomme/squirrel-prover:latest

One can then go inside the docker image with

$ docker run -it cjacomme/squirrel-prover:latest bash

This should open a bash *inside* the docker, which means that you are inside a virtual linux machine separate from your computer. You should land inside a folder with access to the `examples` folder of the squirrel prover repository. You can then move inside this folder `cd examples` and then run one of the examples with `emacs basic-hash.sp`. You will through this basic command only have access to emacs inside the terminal, and not have access to files on your computer.

## Accessing files from outside the docker

To access files from a folder on your computer at `<path_to_your_workspace>`, run 
$ docker run -it -v <path_to_your_workspace>:/opt/squirrel-prover/MyComputer cjacomme/squirrel-prover:latest bash 

This will populate the `MyComputer` folder, next to the `examples` one, with the given path.


## Runing emacs in GUI mode

The simplest way to display a gui emacs is by using a webserver, using a second docker image. Obtain it with:
$ docker pull jare/x11-bridge:latest

Then, run one after another the commands:
```
docker run -d \
 --name x11-bridge \
 -e MODE="tcp" \
 -e XPRA_HTML="yes" \
 -e DISPLAY=:14 \
 -e XPRA_PASSWORD=111 \
 -p 10000:10000 \
 jare/x11-bridge

docker run -d \
 --name emacs-sp \
 --volumes-from x11-bridge \
 -e DISPLAY=:14 \
 cjacomme/squirrel-prover emacs
 ```

Then, visit `http://localhost:10000/index.html?encoding=rgb32&password=111` to obtain a display of a gui emacs, in which you can open files inside the docker. Before opening a file, we recomend that you resize the emacs window to be larger by a drag and drop on the top left corner of the emacs window (inside the browser). Making the window full screen may lead to low resolution and lags.

To kill the dockers, simply run `docker rm -f x11-bridge emacs-sp` (kills both dockers). You can add your own folder in a similar fashion as before, by replacing the commands with
```
docker run -d \
 --name x11-bridge \
 -e MODE="tcp" \
 -e XPRA_HTML="yes" \
 -e DISPLAY=:14 \
 -e XPRA_PASSWORD=111 \
 -v <path_to_your_workspace>:/opt/squirrel-prover/MyComputer \
 -p 10000:10000 \
 jare/x11-bridge
 
docker run -d \
 --name emacs-sp \
 --volumes-from x11-bridge \
 -e DISPLAY=:14 \
 cjacomme/squirrel-prover emacs
 ```

# Compiling and pushing the docker

Run `./docker/build.sh` to build from scratch the image. `docker/res` contains the .emacs used by the docker, as well as the updated `proof-site.el` file from a fixed commit of PG.

To publish the image, see @Charlie JACOMME (Dockerhub does not support free organizations...), which is then done by running:
$ docker tag sp/squirel-prover cjacomme/squirrel-prover:latest; docker push cjacomme/squirrel-prover:latest


