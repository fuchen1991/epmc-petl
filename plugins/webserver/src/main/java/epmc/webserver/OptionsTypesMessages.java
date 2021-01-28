package epmc.webserver;

public final class OptionsTypesMessages {
    public static enum TimeStampFormat {
        NONE,
        JAVA_DATE,
        MILLISECONDS_STARTED,
        MILLISECONDS_ABSOLUTE,
        SECONDS_STARTED,
        SECONDS_ABSOLUTE
    }

    private OptionsTypesMessages() {
    }
}