# set base image
FROM python:3.9.1

# create logs folder and file
RUN mkdir /var/log/hpimdm/
RUN touch /var/log/hpimdm/stdout0

# install hpim-dm
RUN pip3 install hpim-dm

# container will tail logs file
CMD hpim-dm -v
