FROM maven:3.9.9-eclipse-temurin-17

WORKDIR /workspace/q-guard
COPY pom.xml ./
COPY src ./src
RUN mvn -B compile

CMD ["mvn", "exec:java", "-Dexec.mainClass=quantum.Main"]
