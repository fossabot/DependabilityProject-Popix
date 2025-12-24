# Pop!x – Configuration & Build Guide

## Overview

Pop!x is a Java web application developed using **Maven** and packaged as a **WAR** file.  
The project is designed to be **buildable and executable both locally and in CI/CD environments**, using standard and reproducible tooling.

The application can be built:
- locally, using Maven
- in a containerized environment, using Docker and Docker Compose

---

## Project Structure (Relevant Files)

    .
    ├── pom.xml                 # Maven configuration
    ├── Dockerfile              # Application container image
    ├── docker-compose.yml      # Application + database orchestration
    ├── src/
    │   ├── main/               # Application source code
    │   ├── test/               # Automated tests
    │   └── database/           # SQL initialization scripts
    └── target/                 # Build artifacts (generated)

---

## Requirements

### Local Build
- Java JDK 17 or higher
- Maven 3.8 or higher

### Containerized Build
- Docker
- Docker Compose

No IDE-specific configuration is required.

---

## Local Build (Without Docker)

The application can be built locally using the standard Maven lifecycle.

### Build and Test

    mvn clean test

This command:
- compiles the source code
- executes all automated tests
- generates test reports in `target/surefire-reports`

### Package

    mvn clean package

This command produces the deployable artifact:

    target/popix-1.0-SNAPSHOT.war

The generated WAR file can be deployed on any Servlet container compliant with the Jakarta EE specification (e.g. Apache Tomcat).

---

## Containerized Build (Docker)

The application can also be built and executed in a fully isolated environment using Docker.

### Build Containers

    docker compose build

This step:
- builds the application Docker image
- packages the application using Maven inside the container

### Run Application

    docker compose up

This will start:
- the application container (Tomcat)
- the MySQL database container

The database is automatically initialized using the SQL scripts located in:

    src/database/
    ├── 01-createDB.sql
    └── 02-InsertDB.sql

No manual database setup is required.

---

## Environment Configuration

Environment variables are used to configure the database connection and are injected at runtime through Docker Compose.

Example variables:
- `MYSQL_ROOT_PASSWORD`
- `MYSQL_USER`
- `MYSQL_PASSWORD`
- `MYSQL_DATABASE`

These variables allow the same configuration approach to be reused both locally and in CI/CD pipelines.

---

## CI/CD Compatibility

The project is fully compatible with CI/CD pipelines because:

- it relies on **standard Maven commands**
- the build is **fully automated**
- no interactive or manual steps are required
- no IDE-specific configuration is needed
- all dependencies are declared in `pom.xml`
- containerized builds run in isolated environments

A CI pipeline can build the project using either of the following commands:

    mvn clean test package

or

    docker compose build

Both approaches are reproducible and suitable for headless execution environments.

---

## Build Artifacts

- WAR file:  
  `target/popix-1.0-SNAPSHOT.war`

- Test reports:  
  `target/surefire-reports/`

These artifacts can be archived or published by a CI/CD pipeline.

---

## Summary

Pop!x is designed to be:
- buildable locally
- buildable in CI/CD pipelines
- reproducible and automated
- independent from development environments

The use of Maven and Docker ensures portability, reliability, and ease of integration in continuous integration workflows.
